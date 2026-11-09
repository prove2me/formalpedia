-- Prove2me | Theorems.Thm_BosonicLearn_lemma_8
-- name    : BosonicLearn.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:35:52.381293+00:00
-- url     : https://prove2.me/theorems/393931b1-11b1-43f7-9834-8949bffada8d
-- title:
--   Lemma 8 — $\Phi_{X_0}$ is near-isometric, bi-Lipschitz in every Schatten norm, stays in $G_{\mathrm{supp}}$, and has Jacobian $\ge e^{-C'n^2}$
-- statement:
--   There are absolute constants $C,C'>0$ and $\xi_0\in(0,1/32)$ such that for every $n$, every $\xi\in(0,\xi_0]$, every $X_0\in G_{\mathrm{good}}$, every $b\le0.1$, all $Z,Z_1,Z_2\in B_{\mathrm{op},b}(0)$ and every $p\in[1,\infty]$:
--
--   1. $\|D\Phi_{X_0}(Z)[H]-H\|_p\le C\xi\|H\|_p$ for all $H\in\mathrm{Herm}_0(n)$;
--   2. $\tfrac12\|Z_1-Z_2\|_p\le\|\Phi_{X_0}(Z_1)-\Phi_{X_0}(Z_2)\|_p\le2\|Z_1-Z_2\|_p$;
--   3. $\Phi_{X_0}(Z)\in G_{\mathrm{supp}}$;
--   4. $J_{\Phi_{X_0}}(Z)=|\det D\Phi_{X_0}(Z)|\ge\exp(-C'n^2)$.
--
--   These properties let the posterior argument change variables from $X$ to the relative coordinate $Z$.
--
--   Differences from the source:
--   - encoding: ξ ∈ (0, 1/32) "a sufficiently small parameter" (standing assumption of §5.1) → ∃ ξ₀ ∈ (0, 1/32), ∀ ξ ∈ (0, ξ₀]; reason: the proof needs Cξ ≤ ½ for (36), Eq. (50)
--   - encoding: DΦ_{X₀}(Z)[H] := d/dt|_{t=0} Φ_{X₀}(Z + tH) and det(DΦ_{X₀}(Z)) → the Fréchet derivative of Φ_{X₀} on Herm₀(n), applied to H, and the determinant of that real-linear map; reason: Φ_{X₀} is smooth on the domain, so the Fréchet derivative evaluates to the directional derivative
--   - encoding: constants C, C′ → ∃ C, C′ > 0 before n; reason: §5.1: constants independent of n and ε
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 8, Eqs. (35)–(38), pp. 31–32

import Mathlib
import Definitions.Def_BosonicLearn_PhiMap
import Definitions.Def_BosonicLearn_Ggood
import Definitions.Def_BosonicLearn_Gsupp
import Definitions.Def_BosonicLearn_herm0Ball

open scoped ENNReal

namespace BosonicLearn

/-- **Lemma 8 (relative parametrization: derivative, bi-Lipschitz, support, Jacobian).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 8, Eqs. (35)–(38), pp. 31–32: "For any X_0 ∈ G_good and Z, Z_1, Z_2 ∈ B_{op,b}(0) with b ≤ 0.1, and for
every p ∈ [1, ∞], ‖DΦ_{X_0}(Z)[H] − H‖_p ≤ Cξ‖H‖_p, for any H ∈ Herm_0(n). Here DΦ_{X_0}(Z)[H] := d/dt|_{t=0}
Φ_{X_0}(Z + tH). … Consequently, ½‖Z_1 − Z_2‖_p ≤ ‖Φ_{X_0}(Z_1) − Φ_{X_0}(Z_2)‖_p ≤ 2‖Z_1 − Z_2‖_p. Also,
Φ_{X_0}(Z) ∈ G_supp. Finally, the Jacobian determinant of Φ_{X_0} satisfies J_{Φ_{X_0}}(Z) := |det(DΦ_{X_0}(Z))| ≥
exp(−C′n²)."

There are absolute constants `C, C′ > 0` and `ξ₀ ∈ (0, 1/32)` such that for all `n`, all `ξ ∈ (0, ξ₀]`, all
`X₀ ∈ G_good`, all `b ≤ 0.1`, all `Z, Z₁, Z₂ ∈ B_{op,b}(0)` and all `p ∈ [1, ∞]`, the four conclusions (35)–(38) hold.

**Formalization Note.** `ξ ∈ (0, 1/32)` "sufficiently small" is the standing assumption of §5.1 (p. 30); (36) needs
`Cξ ≤ ½` (proof, Eq. (50)), whence `ξ₀`. `DΦ_{X₀}(Z)` is the Fréchet derivative of `Φ_{X₀}` on `Herm₀(n)`, whose value on
`H` is the directional derivative of the page; the Jacobian is the determinant of this real-linear endomorphism of
`Herm₀(n)`. -/
theorem lemma_8 :
    ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
      ∀ (n : ℕ) (ξ : ℝ), 0 < ξ → ξ ≤ ξ₀ → ∀ X₀ ∈ Ggood n, ∀ b : ℝ, b ≤ 1 / 10 →
        ∀ Z ∈ herm0Ball ⊤ 0 b, ∀ Z₁ ∈ herm0Ball ⊤ 0 b, ∀ Z₂ ∈ herm0Ball ⊤ 0 b,
        ∀ p : ℝ≥0∞, 1 ≤ p →
          (∀ H : Herm0 n,
            WHMultiplicativity.schattenNorm p ((fderiv ℝ (PhiMap X₀ ξ) Z H - H : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤
              C * ξ * WHMultiplicativity.schattenNorm p (H : Matrix (Fin n) (Fin n) ℂ)) ∧
          (1 / 2 * WHMultiplicativity.schattenNorm p ((Z₁ - Z₂ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤
              WHMultiplicativity.schattenNorm p ((PhiMap X₀ ξ Z₁ - PhiMap X₀ ξ Z₂ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ∧
            WHMultiplicativity.schattenNorm p ((PhiMap X₀ ξ Z₁ - PhiMap X₀ ξ Z₂ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤
              2 * WHMultiplicativity.schattenNorm p ((Z₁ - Z₂ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ)) ∧
          PhiMap X₀ ξ Z ∈ Gsupp n ∧
          Real.exp (-(C' * (n : ℝ) ^ 2)) ≤
            |LinearMap.det (fderiv ℝ (PhiMap X₀ ξ) Z : Herm0 n →ₗ[ℝ] Herm0 n)| := by sorry

end BosonicLearn
