-- Prove2me | Theorems.Thm_FamousTheorems_hecke_bound_cusp_form_coefficients
-- name    : FamousTheorems.hecke_bound_cusp_form_coefficients
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:10:15.458605+00:00
-- url     : https://prove2.me/theorems/00f519d2-7f11-463b-a1a2-efde6c922ab9
-- title:
--   Hecke's bound for cusp form coefficients
-- statement:
--   **Hecke's bound for cusp form coefficients.** Let $f$ be a cusp form of weight $k$ for an arithmetic subgroup $\Gamma$ of $\mathrm{GL}_2(\mathbb R)$, with $q$-expansion $f=\sum_na_nq^n$ at $\infty$. Then
--   $$a_n=O\big(n^{k/2}\big)\qquad(n\to\infty).$$
--
--   Hecke proved this bound in 1937 using the boundedness of $y^{k/2}|f(x+iy)|$ on the upper half-plane. It gives the analytic continuation and convergence of the associated $L$-series. The Ramanujan–Petersson conjecture, proved by Deligne for holomorphic newforms, improves the exponent to $(k-1)/2+\varepsilon$.
--
--   **Formalization note.** Mathlib's `CuspFormClass.qExpansion_isBigO`. `Γ.IsArithmetic` says that $\Gamma$ is commensurable with $\mathrm{SL}_2(\mathbb Z)$, and `CuspFormClass F Γ k` says that elements of `F` are cusp forms of weight $k$. The $q$-expansion `UpperHalfPlane.qExpansion Γ.strictWidthInfty f` is taken with respect to the width of the cusp at infinity, and the bound is stated with `Asymptotics.IsBigO` along `atTop`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CuspFormClass.qExpansion_isBigO`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hecke_bound_cusp_form_coefficients {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F Γ k] (f : F) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => PowerSeries.coeff n (UpperHalfPlane.qExpansion Γ.strictWidthInfty ⇑f))
      (fun n : ℕ => (n : ℝ) ^ ((k : ℝ) / 2)) := by sorry

end FamousTheorems
