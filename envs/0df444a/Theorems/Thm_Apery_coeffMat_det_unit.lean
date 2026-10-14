-- Prove2me | Theorems.Thm_Apery_coeffMat_det_unit
-- name    : Apery.coeffMat_det_unit
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T20:38:19.853982+00:00
-- url     : https://prove2.me/theorems/fcf8558c-2839-477d-95ae-2b84b9fa1a97
-- title:
--   Unimodularity: $\det(\mathrm{coeffMat}\,E) \neq 0$ and $v_p = 0$ for the class bases
-- statement:
--   **Unimodularity of the class bases.** Let $E_a \in \mathbb{Z}[t]$ ($a \in Fin\\,h$) be congruent modulo $p$ to $\prod_{c \neq \mathrm{cls}\,a} (t - \gamma_c)^{L_c} \cdot (t - \gamma_{\mathrm{cls}\,a})^{\mathrm{idx}\,a}$, where the $\gamma_c \in \mathbb{F}_p$ are distinct, $\mathrm{idx}\,a < L_{\mathrm{cls}\,a}$ and $(\mathrm{cls},\mathrm{idx})$ is injective. Then the rational coefficient matrix of the $E_a$ has determinant nonzero and prime to $p$. This is `coeffMat_det_unit` of `Apery/Arith/Unimodular.lean` (with the auxiliary `sum_pow_X_sub_C_eq_zero`, `classBasis_independent`); the matrix `coeffMat E = Matrix.of fun a k => (E a).coeff k` is written out with explicit index types in the statement. It is the unimodularity input of the class-basis framework `class_frame` toward `Apery.inner_bound_cap`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/Unimodular.lean (+ BasisChange.lean coeffMat, DirectBound.lean padicValRat_int_eq_zero)

import Mathlib

open Finset Polynomial Matrix

namespace Apery

theorem coeffMat_det_unit {h : ℕ} {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Ez : Fin h → ℤ[X]) (hdeg : ∀ a, (Ez a).natDegree < h)
    (γ : ι → ZMod p) (hγ : Function.Injective γ) (L : ι → ℕ) (cls : Fin h → ι) (idx : Fin h → ℕ)
    (hidx : ∀ a, idx a < L (cls a)) (hinj : ∀ a b, cls a = cls b → idx a = idx b → a = b)
    (hred : ∀ a, (Ez a).map (Int.castRingHom (ZMod p)) =
      (∏ c ∈ Finset.univ.erase (cls a), (X - C (γ c)) ^ L c) * (X - C (γ (cls a))) ^ idx a) :
    (Matrix.of (fun a k => ((Ez a).map (Int.castRingHom ℚ)).coeff k : Fin h → Fin h → ℚ)).det ≠ 0 ∧
      padicValRat p (Matrix.of (fun a k => ((Ez a).map (Int.castRingHom ℚ)).coeff k : Fin h → Fin h → ℚ)).det = 0 := by
  sorry

end Apery
