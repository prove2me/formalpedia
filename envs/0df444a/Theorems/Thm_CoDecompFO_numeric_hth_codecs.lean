-- Prove2me | Theorems.Thm_CoDecompFO_numeric_hth_codecs
-- name    : CoDecompFO.numeric_hth_codecs
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:40:09.786068+00:00
-- url     : https://prove2.me/theorems/6143603f-c844-4f4a-a2b9-a7f15111a40c
-- title:
--   Concrete primitive-recursive encoders for induced tables, reduced pullbacks, and alternating evaluation
-- statement:
--   Implement the tables of reduced hypotheticals by natural numbers. For fixed $\sigma$ there are primitive-recursive functions $\mathrm{leaf}$, $\mathrm{join}$, and $\mathrm{acc}$ on length-prefixed lists of natural numbers, and a computable bound $B(w,|\varphi|)$, such that for every sentence $\varphi$ there are numeric codes of reduced $(2\ell,\ell)$-hypotheticals with $\ell=\operatorname{quantCount}(\varphi)$ satisfying:
--   - $\mathrm{leaf}$ codes the hypothetical induced by the full strategy over a bag;
--   - $\mathrm{join}$ codes the projection to the parent of the reduced pullback of the two tables, from the bags, adhesion, homomorphisms, and child and parent table codes;
--   - every code over a bag of size $n\le w$ is at most $B(w,|\varphi|)$;
--   - $0\le\mathrm{acc}\le1$, and $\mathrm{acc}$ agrees with alternating evaluation of $\operatorname{altMatrix}(\varphi)$ on every coded table;
--   - when the root fold is over an empty limit, $\mathrm{acc}$ instead gives truth of $\varphi$ in that empty structure, using nullary information carried by the root table.
--
--   The finite universe needed here is supplied independently by the explicit tower bound of Lemma 5.81. This child isolates the actual bit-table/list encoders and decoders from the tree induction and alternating root semantics.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶5.80 and the proof of Theorem 1.16, p.41: compute reduced hypotheticals bottom-up and stop when the bound forces repetition; Lemma 5.81 and ¶5.82, p.41 for the finite bound; the corrected alternating evaluation described in the root test of Theorem 1.16; A.7–A.9, p.53 for equality and nullary relations. The statement formalizes the finite numeric encoding step implicit in the paper's RAM algorithm.

import Mathlib
import Definitions.Def_CoDecompFO_AltMatrix
import Definitions.Def_CoDecompFO_Fold
import Definitions.Def_CoDecompFO_CodeFold
import Definitions.Def_CoDecompFO_Codes

set_option autoImplicit false

open FirstOrder
open CoDecompFO

/-- Concrete numeric hypothetical tables: primitive-recursive local operations, their semantic
correctness, a computable table bound, and alternating evaluation including empty limits. -/
theorem CoDecompFO.numeric_hth_codecs (σ : Sig) :
    ∃ (leaf join acc : List ℕ → ℕ) (B : ℕ → ℕ → ℕ),
      Primrec leaf ∧ Primrec join ∧ Primrec acc ∧
      (∀ v, acc v ≤ 1) ∧ Computable₂ B ∧
      ∀ (φ : σ.lang.Sentence) (w : ℕ),
        ∃ code : ∀ {n : ℕ}, HTh (sigmaEq σ) (Fin n) (2 * quantCount φ) (quantCount φ) → ℕ,
          (∀ A : Bag σ,
            code (ind (sigmaEq σ) (2 * quantCount φ) (quantCount φ)
              (Strat.full (Fin A.withEq.n) (quantCount φ)) []) =
              leaf (frame [encF φ, encBag A])) ∧
          (∀ (A D K : Bag σ) (g : Fin D.n → Fin K.n) (h : Fin A.n → Fin K.n)
            (H : HTh (sigmaEq σ) (Fin A.n) (2 * quantCount φ) (quantCount φ))
            (Hc : HTh (sigmaEq σ) (Fin D.n) (2 * quantCount φ) (quantCount φ)),
            code (push (Fib.snd : Fib g h → Fin A.n) (quantCount φ) (pb g h (quantCount φ) Hc H)) =
              join (frame [encF φ, encBag A, encBag D, encBag K,
                List.ofFn (fun x => (h x).val), List.ofFn (fun x => (g x).val),
                [code H], [code Hc] ])) ∧
          (∀ (n : ℕ) (H : HTh (sigmaEq σ) (Fin n) (2 * quantCount φ) (quantCount φ)),
            n ≤ w → code H ≤ B w (sentLen φ)) ∧
          (∀ (n : ℕ) (H : HTh (sigmaEq σ) (Fin n) (2 * quantCount φ) (quantCount φ)),
            (acc (frame [encF φ, [code H] ]) = 1 ↔
              eval (altMatrix φ) (quantCount φ) H)) ∧
          (∀ T : CoDecomp σ, width T ≤ w → ∀ (r : Fin T.b) (v : ℕ),
            T.CodeFold r (encF φ) leaf join r Set.univ v →
            IsEmpty T.Lim →
            ((acc (frame [encF φ, [v] ]) = 1) ↔ T.Lim ⊨ φ)) := by sorry
