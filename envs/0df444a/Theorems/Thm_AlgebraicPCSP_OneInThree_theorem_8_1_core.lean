-- Prove2me | Theorems.Thm_AlgebraicPCSP_OneInThree_theorem_8_1_core
-- name    : AlgebraicPCSP.OneInThree.theorem_8_1_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:28.271661+00:00
-- url     : https://prove2.me/theorems/447fd463-e3d9-486c-a8e2-8aeea9e10345
-- title:
--   Theorem 8.1 (algebraic core) — no finite D with 1-in-3 → D → NAE has a cyclic polymorphism of prime arity p > 60|D|
-- statement:
--   Let $D$ be a finite set and $R\subseteq D^3$. Suppose $f:\{0,1\}\to D$ is a homomorphism from the 1-in-3 structure $\mathbf T$ to $(D;R)$, and $g:D\to\{0,1\}$ is a homomorphism from $(D;R)$ to the not-all-equal structure $\mathbf H_2$; that is, $(\mathbf T,\mathbf H_2)$ is a homomorphic relaxation of $((D;R),(D;R))$:
--   $$\mathbf T\xrightarrow{\ f\ }(D;R)\xrightarrow{\ g\ }\mathbf H_2 .$$
--   Let $p$ be a prime with $p>60\,|D|$. Then $(D;R)$ has **no** cyclic polymorphism $s:D^p\to D$, i.e. no polymorphism with $s(a_1,a_2,\dots,a_p)=s(a_2,\dots,a_p,a_1)$ for all $a\in D^p$.
--
--   Theorem 8.1 of the paper states that if $(\mathbf T,\mathbf H_2)$ is pp-constructible from a finite relational structure $\mathbf D$, then $\mathrm{CSP}(\mathbf D)$ is NP-complete. Its proof (i) uses Theorem 4.12 to turn pp-constructibility into a homomorphic relaxation of a pp-power of $\mathbf D$, (ii) uses that a pp-power of a finite tractable CSP template is a finite tractable CSP template, so the pp-power may be taken to be $\mathbf D$ itself with a single ternary relation, and (iii) invokes the theorem of Barto and Kozik [BK12] (Theorem 8.3) that a finite $\mathbf D$ whose CSP is not NP-complete has a cyclic polymorphism of every prime arity $p>|D|$. What remains, and what is stated here, is the combinatorial contradiction of §8.2–8.4.
--
--   The result shows that 1-in-3 versus Not-All-Equal-SAT, although solvable in polynomial time, cannot be solved by reduction to any finite tractable CSP; infinite templates are necessary.
--
--   **Formalization Note** The complexity conclusion, steps (i)–(ii) and the cited Theorem 8.3 are not formalized; the statement is the contrapositive core. The paper renames $D$ so that $f(0)=0$, $f(1)=1$; here $f$ is kept. The hypotheses on $s$ are exactly "polymorphism of $(D;R)$" and "cyclic"; nothing like idempotence or count-dependence is assumed.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 52, Theorem 8.1 (algebraic core established by the proof, pp. 52–58)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices

namespace AlgebraicPCSP.OneInThree

open PCSPBLPAff.Symmetric

/-- Theorem 8.1 (p. 52), algebraic core: let `D` be a finite set and `R ⊆ D³`, and let
`f : T → (D; R)` and `g : (D; R) → H₂` be homomorphisms, where `T` is 1-in-3 and `H₂` is
not-all-equal on `{0, 1}`. Then `(D; R)` has no cyclic polymorphism of prime arity
`p > 60|D|`. -/
theorem theorem_8_1_core {D : Type} [Fintype D] [DecidableEq D] (R : Set (Fin 3 → D))
    (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    (p : ℕ) (hp : p.Prime) (hpD : 60 * Fintype.card D < p)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) :
    False := by sorry

end AlgebraicPCSP.OneInThree
