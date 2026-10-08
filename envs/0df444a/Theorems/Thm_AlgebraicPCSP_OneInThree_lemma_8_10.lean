-- Prove2me | Theorems.Thm_AlgebraicPCSP_OneInThree_lemma_8_10
-- name    : AlgebraicPCSP.OneInThree.lemma_8_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:20.303691+00:00
-- url     : https://prove2.me/theorems/b8179049-c491-487f-afe6-b07b80a2b821
-- title:
--   Lemma 8.10 — every ⟨i⟩ is tame, and ⟨0⟩ ≁ ⟨p²⟩
-- statement:
--   In the setting of Lemma 8.9 ($f:\mathbf T\to(D;R)$, $g:(D;R)\to\mathbf H_2$ homomorphisms, $s$ a cyclic polymorphism of $(D;R)$ of prime arity $p>3$), each line segment $\langle i\rangle$, $i\in\{0,1,\dots,p^2\}$, is tame, and
--   $$\langle 0\rangle\not\sim\langle p^2\rangle,$$
--   i.e. the all-zero matrix $0_{p\times p}$ and the all-one matrix $1_{p\times p}$ are not $g$-equivalent.
--
--   This is the base case of the induction that shows almost rectangles are tame (Proposition 8.12), and its second part is the source of the final contradiction.
--
--   **Formalization Note** $\langle 0\rangle$ is the zero matrix and $\langle p^2\rangle$ the all-one matrix. As in Lemma 8.9, $p>60|D|$ is replaced by $p>3$.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 55, Lemma 8.10

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices

namespace AlgebraicPCSP.OneInThree

open PCSPBLPAff.Symmetric

/-- Lemma 8.10 (p. 55): each `⟨i⟩`, `i ∈ {0, 1, …, p²}`, is tame, and `⟨0⟩ ≁ ⟨p²⟩`
(i.e. `0_{p×p} ≁ 1_{p×p}`), for a cyclic polymorphism `s` of `(D; R)` of prime arity
`p > 3` and homomorphisms `f : T → (D; R)`, `g : (D; R) → H₂`. -/
theorem lemma_8_10 {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) :
    (∀ i, i ≤ p * p → IsTame f g s (seg p i)) ∧
    ¬ GEquiv f g s (seg p 0) (seg p (p * p)) := by sorry

end AlgebraicPCSP.OneInThree
