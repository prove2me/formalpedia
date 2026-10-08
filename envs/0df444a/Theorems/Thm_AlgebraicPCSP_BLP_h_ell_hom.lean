-- Prove2me | Theorems.Thm_AlgebraicPCSP_BLP_h_ell_hom
-- name    : AlgebraicPCSP.BLP.h_ell_hom
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:06.638637+00:00
-- url     : https://prove2.me/theorems/9f70f588-f6ad-417e-8880-0a42403cec49
-- title:
--   Proof of Theorem 7.9, p. 48 — a symmetric polymorphism of arity ℓ gives a homomorphism LP_ℓ(A) → B
-- statement:
--   Let $(\mathbf A,\mathbf B)$ be similar structures with $A$ finite, and let $\ell\ge 1$. If $\mathrm{Pol}(\mathbf A,\mathbf B)$ contains a symmetric function $s_\ell$ of arity $\ell$, i.e. a polymorphism with
--   $$s_\ell(x_{\pi(1)},\dots,x_{\pi(\ell)})=s_\ell(x_1,\dots,x_\ell)\quad\text{for every permutation }\pi\text{ of }[\ell],$$
--   then $\mathrm{LP}_\ell(\mathbf A)$ maps homomorphically to $\mathbf B$.
--
--   In the paper the homomorphism is $h_\ell(\phi)=s_\ell(a_1,\dots,a_\ell)$, where each $a\in A$ appears exactly $\phi(a)\ell$ times among $a_1,\dots,a_\ell$. Since every finite substructure of $\mathrm{LP}(\mathbf A)$ is a substructure of some $\mathrm{LP}_\ell(\mathbf A)$, this step together with compactness yields $\mathrm{LP}(\mathbf A)\to\mathbf B$, and hence item (1) of Theorem 7.9, from item (2).
--
--   **Formalization Note** Only the existence of the homomorphism is asserted, which is what the sentence "every $\mathrm{LP}_\ell(\mathbf A)$ maps homomorphically to $\mathbf B$" states.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 48, proof of Theorem 7.9 (definition of h_ℓ : LP_ℓ(A) → B)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_BLP_LP

namespace AlgebraicPCSP.BLP

open PCSPBLPAff.Symmetric

/-- Proof of Theorem 7.9, p. 48 (arXiv:1811.00970v3): for `ℓ ≥ 1`, if `Pol(𝔸, 𝔹)` contains a
symmetric function `s_ℓ` of arity `ℓ`, then `LP_ℓ(𝔸)` maps homomorphically to `𝔹` (the paper's
`h_ℓ(ϕ) = s_ℓ(a₁, …, a_ℓ)`, each `a` appearing `ϕ(a)ℓ` times, is such a homomorphism). -/
theorem h_ell_hom {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hs : ∃ s : (Fin ℓ → A) → B, IsPolymorphism 𝔸 𝔹 s ∧ IsSymmetric s) :
    ∃ h : LPellDist A ℓ → B, IsHom (LPell 𝔸 ℓ) 𝔹 h := by sorry

end AlgebraicPCSP.BLP
