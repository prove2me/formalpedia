-- Prove2me | Theorems.Thm_CoDecompFO_fold_codes
-- name    : CoDecompFO.fold_codes
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T23:44:12.694271+00:00
-- url     : https://prove2.me/theorems/0e0415f3-b1a8-4c45-ac39-c0514c11cab9
-- title:
--   Tables of hypotheticals as numbers: primitive recursive operations and a computable bound
-- statement:
--   Fix a finite relational signature $\sigma$. This statement says that the tables of hypotheticals of the proof of Theorem 1.16, and the operations performed on them, can be carried out on numbers by primitive recursive functions, with tables of bounded size. No machine occurs in it.
--
--   There are primitive recursive functions $\mathrm{leaf}$, $\mathrm{join}$, $\mathrm{acc}$ from lists of numbers to numbers, with $\mathrm{acc}\le 1$, and a computable function $B$ such that for every first-order $\sigma$-sentence $\varphi$ with equality and every tree co-decomposition $\mathcal T$ of width at most $w$ the following hold. Consider bottom-up computations with numeric tables on $\mathcal T$, with parameter the code $\langle\varphi\rangle$ of $\varphi$: a node alone gets $\mathrm{leaf}$ of $\langle\varphi\rangle$ and the code of its bag, and absorbing a child's subtree applies $\mathrm{join}$ to $\langle\varphi\rangle$, the codes of the two bags, of the adhesion and of the two maps, and the two tables.
--
--   1. **Bounded tables.** Every table $v$ of such a computation, at every node and for every root, satisfies
--
--   $$
--   v\le B(w,|\varphi|).
--   $$
--
--   2. **Non-empty limit.** Let $v$ be a root table. If $\lim\mathcal T\neq\emptyset$, then there is a root table $H$ of the bottom-up computation of hypotheticals over $\mathcal T^\circ$, with $\ell$ the number of quantifiers of $\varphi$ and $2\ell$ variables, such that $\mathrm{acc}(\langle\varphi\rangle,v)=1$ if and only if $H$ passes alternating evaluation of the matrix $\psi$ of the alternating form of $\varphi$.
--   3. **Empty limit.** If $\lim\mathcal T=\emptyset$, then $\mathrm{acc}(\langle\varphi\rangle,v)=1$ if and only if $\lim\mathcal T\models\varphi$.
--
--   Clause 1 is the content of Lemma 5.81 for an explicit representation: the reduced hypotheticals over a bag of at most $w$ points are finitely many, with a bound depending on $w$ and $|\varphi|$ only. Together with a linear-time bottom-up traversal on a word RAM, the statement gives the algorithm of Theorem 1.16.
--
--   **Formalization Note** The numeric computation is `CoDecomp.CodeFold`, the computation of hypotheticals is `CoDecomp.IsFold` on `T.withEq`, the matrix is `altMatrix φ` with $\ell$ = `quantCount φ`, and alternating evaluation is `eval`. Arguments are passed as one list, each preceded by its length (`frame`). On an empty limit every universal quantifier holds, and the truth of $\varphi$ depends only on the nullary relations of the bags.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Lemma 5.81 and ¶5.82, p.41; proof of Theorem 1.16, p.41; Observation 5.79 and ¶5.80, p.41; A.7–A.9, p.53

import Mathlib
import Definitions.Def_CoDecompFO_AltMatrix
import Definitions.Def_CoDecompFO_Fold
import Definitions.Def_CoDecompFO_CodeFold
import Definitions.Def_CoDecompFO_Codes

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Tables of hypotheticals as numbers** (Bumpus et al., *Co-Decompositions and FO Model Checking*,
arXiv:2611.04658, held file sha256 d550d7af…, Lemma 5.81, p.41: "For fixed signature σ, formula φ, and
width w, the number of reduced hypotheticals that can occur over a bag of size at most w is bounded by a
function of w and |φ|"; proof of Theorem 1.16, p.41; ¶5.80, p.41).

For each `σ` there are primitive recursive functions `leaf`, `join`, `acc` on lists of numbers and a
computable bound `B` such that, for every `φ` and every `T` of width at most `w`: every table of a
bottom-up computation with `leaf` and `join` on the code of `φ` is at most `B(w,|φ|)`; and for a root
table `v`, `acc` on the code of `φ` and `v` is `1` or `0`, and it is `1` iff, when the limit is non-empty,
some root table `H` of the bottom-up computation of hypotheticals over `T°` passes alternating evaluation
of `altMatrix φ`, and, when the limit is empty, `φ` holds in it.

**Formalization Note** No machine occurs. On an empty limit every `∀` holds and the alternating form is not
equivalent to `φ`; the truth of `φ` then depends only on the nullary relations of the bags, which the
tables may carry. -/
theorem fold_codes (σ : Sig) :
    ∃ (leaf join acc : List ℕ → ℕ) (B : ℕ → ℕ → ℕ),
      Primrec leaf ∧ Primrec join ∧ Primrec acc ∧ (∀ l, acc l ≤ 1) ∧ Computable₂ B ∧
      ∀ (T : CoDecomp σ) (φ : σ.lang.Sentence) (w : ℕ), width T ≤ w →
        (∀ (r t : Fin T.b) (S : Set (Fin T.b)) (v : ℕ),
          T.CodeFold r (encF φ) leaf join t S v → v ≤ B w (sentLen φ)) ∧
        (∀ (r : Fin T.b) (v : ℕ), T.CodeFold r (encF φ) leaf join r Set.univ v →
          (IsEmpty T.Lim → (acc (frame [encF φ, [v] ]) = 1 ↔ T.Lim ⊨ φ)) ∧
          (Nonempty T.Lim →
            ∃ H : HTh (sigmaEq σ) (Fin (T.withEq.bag r).n) (2 * quantCount φ) (quantCount φ),
              T.withEq.IsFold r (2 * quantCount φ) (quantCount φ) r Set.univ H ∧
              (acc (frame [encF φ, [v] ]) = 1 ↔ eval (altMatrix φ) (quantCount φ) H))) := by sorry

end CoDecompFO
