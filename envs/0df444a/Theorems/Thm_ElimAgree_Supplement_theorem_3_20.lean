-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_3_20
-- name    : ElimAgree.Supplement.theorem_3_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:37:34.783911+00:00
-- url     : https://prove2.me/theorems/d432ead1-12dc-4921-b038-4f4248f2afaf
-- title:
--   Theorem 3.20 (Every message cell keeps its mass)
-- statement:
--   Let $\ell\ge2$, $N=4\ell-1$, $\pi$ uniform on $\Omega=\binom{[N]}\ell$, and $D$, $I$ the conditional-expectation operators of $\mu_D$ and $\mu_I$. Let $k\ge1$ and let $B\subseteq\Omega^k$ have mass $q=\pi^{\otimes k}(B)>0$; put $t=\ln(1/q)+1+\ln2$. Then
--
--   $$\int\min_{\sigma\in\{D,I\}^k}\Big(\bigotimes_i\sigma_i\Big)1_B\,d\pi^{\otimes k}\ \ge\ q\Big(1-\frac{32\sqrt{2e}}{\ell}\sqrt{kt}-\frac{16}{\ell}\,t\Big).$$
--
--   So no set of Bob's inputs of non-negligible mass can be steered by Alice's choice of answers: whichever answer pattern $\sigma$ she picks, the cell keeps almost all of its mass. This is the core of the one-way lower bound (Theorem 3.21).
--
--   **Formalization Note** The minimum is pointwise over the $2^k$ patterns; the integral is the uniform average over $\Omega^k$.
--
--   Differences from the source:
--   - reading: B ⊆ Ω^k (k ≥ 1 implicit) → 1 ≤ k; reason: k is the number of instances
--   - encoding: ∫ … dπ^{⊗k} and D, I as conditional expectations → uniform average over Ω^k; kernels of µ_D, µ_I normalized over Ω; reason: same quantities
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 3.20, p.16 (PDF p.18); §3.8 setting, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_CellMass

namespace ElimAgree

namespace Supplement

/-- Theorem 3.20 (Every message cell keeps its mass), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.16. In §3.8, `ℓ ≥ 2`, `N = 4ℓ − 1`,
`π` is uniform on `Ω = ([N] choose ℓ)`, and `D`, `I` are the conditional-expectation operators of
`µ_D` and `µ_I`. Let `B ⊆ Ω^k` have mass `q = π^{⊗k}(B) > 0`, and put `t = ln(1/q) + 1 + ln 2`. Then
`∫ min_{σ∈{D,I}^k} (⊗_i σ_i) 1_B dπ^{⊗k} ≥ q(1 − (32√(2e)/ℓ)√(kt) − (16/ℓ)t)`.

**Formalization Note.** `k ≥ 1` is the number of instances. The integral is the uniform average
over `Ω^k` of the pointwise minimum over the `2^k` choices of `σ`. -/
theorem theorem_3_20 (ℓ k : ℕ) (hℓ : 2 ≤ ℓ) (hk : 1 ≤ k) (B : Finset (Fin k → Omega ℓ))
    (hq : 0 < piMass ℓ k B) :
    piMass ℓ k B * (1 - 32 * Real.sqrt (2 * Real.exp 1) / ℓ *
        Real.sqrt (k * (Real.log (1 / piMass ℓ k B) + 1 + Real.log 2)) -
      16 / ℓ * (Real.log (1 / piMass ℓ k B) + 1 + Real.log 2)) ≤ minCellIntegral ℓ k B := by sorry

end Supplement

end ElimAgree
