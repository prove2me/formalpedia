-- Prove2me | Theorems.Thm_AlgebraicPCSP_OneInThree_lemma_8_9
-- name    : AlgebraicPCSP.OneInThree.lemma_8_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:12.19963+00:00
-- url     : https://prove2.me/theorems/0d5e3d87-9a36-499c-a24a-5e77467460a2
-- title:
--   Lemma 8.9 — ⟨0⟩ ∼ ⋯ ∼ ⟨q⟩ ≁ ⟨q+1⟩ ∼ ⋯ ∼ ⟨2q+1⟩ where p² = 3q + 1
-- statement:
--   Let $D$, $R\subseteq D^3$, homomorphisms $f:\mathbf T\to(D;R)$ and $g:(D;R)\to\mathbf H_2$ be given, let $p>3$ be a prime and $s:D^p\to D$ a cyclic polymorphism of $(D;R)$. Since $p^2\equiv 1\pmod 3$, write $p^2=3q+1$. For the line segments $\langle i\rangle$ (the $p^2$-tuple with ones in its first $i$ positions),
--   $$\langle 0\rangle\sim\langle 1\rangle\sim\cdots\sim\langle q\rangle\not\sim\langle q+1\rangle\sim\cdots\sim\langle 2q\rangle\sim\langle 2q+1\rangle.$$
--
--   The lemma splits the first $2q+2$ line segments into two $g$-classes at the point where the area crosses $1/3$.
--
--   **Formalization Note** The chain is stated as three conjuncts: $\langle i\rangle\sim\langle 0\rangle$ for $i\le q$; $\langle i\rangle\sim\langle q+1\rangle$ for $q+1\le i\le 2q+1$; and $\langle q\rangle\not\sim\langle q+1\rangle$. $q$ is any natural number with $p\cdot p=3q+1$. The bound $p>60|D|$ of §8 is not needed here and is replaced by $p>3$, the hypothesis the proof uses.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 55, Lemma 8.9 (q from p² = 3q + 1, p. 54)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices

namespace AlgebraicPCSP.OneInThree

open PCSPBLPAff.Symmetric

/-- Lemma 8.9 (p. 55): with `p² = 3q + 1`,
`⟨0⟩ ∼ ⟨1⟩ ∼ ⋯ ∼ ⟨q⟩ ≁ ⟨q + 1⟩ ∼ ⋯ ∼ ⟨2q⟩ ∼ ⟨2q + 1⟩`, for a cyclic polymorphism `s` of
`(D; R)` of prime arity `p > 3` and homomorphisms `f : T → (D; R)`, `g : (D; R) → H₂`. -/
theorem lemma_8_9 {D : Type} (R : Set (Fin 3 → D)) (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) (q : ℕ) (hq : p * p = 3 * q + 1) :
    (∀ i, i ≤ q → GEquiv f g s (seg p i) (seg p 0)) ∧
    (∀ i, q + 1 ≤ i → i ≤ 2 * q + 1 → GEquiv f g s (seg p i) (seg p (q + 1))) ∧
    ¬ GEquiv f g s (seg p q) (seg p (q + 1)) := by sorry

end AlgebraicPCSP.OneInThree
