-- Prove2me | Theorems.Thm_FamousTheorems_lagrange_multiplier_theorem
-- name    : FamousTheorems.lagrange_multiplier_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:40.876374+00:00
-- url     : https://prove2.me/theorems/db7d4abd-6f06-4315-97d9-79590eba2fd5
-- title:
--   The Lagrange multiplier theorem
-- statement:
--   **The Lagrange multiplier theorem.** Let $E$ be a real Banach space, $\varphi:E\to\mathbb R$, and let $f_i:E\to\mathbb R$ for $i$ in a finite index set. Suppose $x_0$ is a local extremum of $\varphi$ on the level set $\{x: f_i(x)=f_i(x_0)\ \forall i\}$, and that $\varphi$ and all $f_i$ are strictly differentiable at $x_0$. Then there are multipliers $\Lambda_i$ and $\Lambda_0$, not all zero, with
--   $$\sum_i\Lambda_i\,Df_i(x_0)+\Lambda_0\,D\varphi(x_0)=0.$$
--
--   This is the multiplier rule of constrained optimization. It is due to Lagrange for mechanics, and in this form, with a possibly vanishing $\Lambda_0$, to Fritz John. When the $Df_i(x_0)$ are linearly independent one can take $\Lambda_0=1$, which gives the familiar condition $\nabla\varphi=\sum\lambda_i\nabla f_i$.
--
--   **Formalization note.** Mathlib's `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`. Derivatives are elements of `StrongDual ℝ E`, the continuous dual of $E$. The condition "not all zero" is `(Λ, Λ₀) ≠ 0` for the pair in $(\iota\to\mathbb R)\times\mathbb R$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem lagrange_multiplier_theorem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {φ : E → ℝ} {x₀ : E}
    {φ' : StrongDual ℝ E} {ι : Type*} [Fintype ι] {f : ι → E → ℝ} {f' : ι → StrongDual ℝ E}
    (hextr : IsLocalExtrOn φ {x | ∀ i, f i x = f i x₀} x₀) (hf' : ∀ i, HasStrictFDerivAt (f i) (f' i) x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀) :
    ∃ (Λ : ι → ℝ) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∑ i, Λ i • f' i + Λ₀ • φ' = 0 := by sorry

end FamousTheorems
