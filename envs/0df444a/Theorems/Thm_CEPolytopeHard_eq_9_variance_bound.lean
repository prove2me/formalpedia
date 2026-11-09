-- Prove2me | Theorems.Thm_CEPolytopeHard_eq_9_variance_bound
-- name    : CEPolytopeHard.eq_9_variance_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:49.451795+00:00
-- url     : https://prove2.me/theorems/fa93f4a6-c634-4b2e-a08d-f33e25894eb5
-- title:
--   Section 3.2, Eq. (9) and the bound $V(s) \le 2(\alpha+\eta)/s$
-- statement:
--   Setting (one layer of Section 3.2): points $x_1, \dots, x_k \in [0,1]^d$, a stochastic matrix $P$ with stationary distribution $\mu$, a map $f$ of $[0,1]^d$ into itself, $\alpha \in (0, 1]$, $\Delta_j = f(x_j) - x_j$, $e_j = x_j - \sum_a P_{ja}(x_a + \alpha\Delta_a)$ (so that $x_j = \mathbb E_{a\sim P_j}[x_a + \alpha\Delta_a] + e_j$), and $\eta$ with $\mathbb E_{j\sim\mu}\|e_j\|_2 \le \eta$. Norms are normalized.
--
--   1. For $0 < s < 1$, both inequalities of (9) hold:
--   $$
--   \mathbb E_{i\sim\mu}\|x_i - \bar x_i(s)\|_2 \le \frac{1-s}{s}\,\mathbb E_{i\sim\mu,\,j\sim P_i(s),\,a\sim P_j}\big[\alpha\|\Delta_a\|_2 + \|e_j\|_2\big] \le \frac{\alpha + \eta}{s}.
--   $$
--   2. For $0 < s \le 1$, $\mathbb E_{i\sim\mu}\|x_i - \bar x_i(s)\|_2 \le (\alpha+\eta)/s$, and
--   $$
--   V(s) \le \mathbb E_{i\sim\mu,\,j\sim P_i(s)}\|x_j - x_i\|_2^2 = \frac2d\,\mathbb E_{i\sim\mu,\,j\sim P_i(s)}\langle x_i - x_j, x_i\rangle = \frac2d\,\mathbb E_{i\sim\mu}\langle x_i - \bar x_i(s), x_i\rangle \le 2\,\mathbb E_{i\sim\mu}\|x_i - \bar x_i(s)\|_2 \le \frac{2(\alpha+\eta)}{s}.
--   $$
--
--   These bound the conditional variance at the scale $s = t_{\ell-1}$ in the support-amplification argument.
--
--   Differences from the source:
--   - generalization: the points of layer ℓ of a fixed set of the lift g, with P, µ from that fixed set, f the circuit map, α = α_ℓ and η = √r ϵ → arbitrary points in [0, 1]^d, any stochastic P with stationary µ, any f mapping [0, 1]^d into itself, any α ∈ (0, 1] and any η ≥ E_µ‖e_j‖₂; reason: the argument uses only these properties, and the layer data of Section 3.2 has them
--   - encoding: expectations over µ, P_i(s), P_j; inner products → finite weighted sums; ⟨u, v⟩ = Σ_c u_c v_c; dimension d = card ι; reason: Lean representation; same values
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 3.2, Eq. (9), p.16, and the V(s) display, pp.16–17 (endpoint s = 1, p.17)

import Mathlib
import Definitions.Def_CEPolytopeHard_nnorm
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_CEPolytopeHard_geo
import Definitions.Def_CEPolytopeHard_condVar

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Eq. (9) and the bound on `V(s)`** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Section 3.2, pp.16–17: "By triangle inequality, and
taking expectations over μ, it follows that E_{i∼μ}∥x_i − x̄_i(s)∥₂ ≤ ((1 − s)/s)
E_{i∼μ,j∼P_i(s),a∼P_j}[α∥∆_a∥₂ + ∥e_j∥₂] ≤ (1/s)(α + η) (9)" and "V(s) ≤ E_{i∼μ,j∼P_i(s)}∥x_j − x_i∥₂²
= (2/d) E_{i∼μ,j∼P_i(s)}⟨x_i − x_j, x_i⟩ = (2/d) E_{i∼μ}⟨x_i − x̄_i(s), x_i⟩ ≤ 2 E_{i∼μ}∥x_i − x̄_i(s)∥₂
≤ (2/s)(α + η)", with "For s = 1, V(1) = 0, so the preceding bound on V(s) also holds at this
endpoint", p.17).

Setting (Section 3.2, pp.16–17, for one layer): points `x_1, …, x_k ∈ [0, 1]^ι`, a stochastic matrix
`P` with stationary distribution `μ`, a map `f` of `[0, 1]^ι` into itself, `α ∈ (0, 1]`,
`Δ_j = f(x_j) − x_j`, `e_j = x_j − ∑_a P_{ja}(x_a + αΔ_a)` (so `x_j = E_{a∼P_j}[x_a + αΔ_a] + e_j`),
and `η` with `∑_j μ_j ‖e_j‖₂ ≤ η`. Norms are normalized (p.9), `D = card ι`.

1. For `0 < s < 1`, both inequalities of (9) hold.
2. For `0 < s ≤ 1`: `E_μ‖x_i − x̄_i(s)‖₂ ≤ (α + η)/s`, and the displayed chain for `V(s)` holds,
   ending in `V(s) ≤ 2(α + η)/s`.

**Formalization Note** The paper states these for the layer `ℓ` of a fixed set of the lifted map;
here the points, the chain and `f` are arbitrary with the properties the argument uses.
Expectations are finite sums; `⟨u, v⟩ = ∑_c u_c v_c` (p.10). -/
theorem eq_9_variance_bound {k : ℕ} {ι : Type} [Fintype ι] (P : Matrix (Fin k) (Fin k) ℝ)
    (hP : IsStochastic P) (μ : Fin k → ℝ) (hμ : IsStationary P μ) (x : Fin k → ι → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ι → ℝ) 1) (f : (ι → ℝ) → ι → ℝ)
    (hf : ∀ y ∈ Set.Icc (0 : ι → ℝ) 1, f y ∈ Set.Icc (0 : ι → ℝ) 1) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (η : ℝ)
    (hη : ∑ j, μ j * nnorm (x j - ∑ a, P j a • (x a + α • (f (x a) - x a))) ≤ η) :
    (∀ s : ℝ, 0 < s → s < 1 →
      ∑ i, μ i * nnorm (x i - xbar P x s i) ≤
        (1 - s) / s * ∑ i, μ i * ∑ j, geo P s i j * ∑ a, P j a *
          (α * nnorm (f (x a) - x a) + nnorm (x j - ∑ c, P j c • (x c + α • (f (x c) - x c)))) ∧
      (1 - s) / s * ∑ i, μ i * ∑ j, geo P s i j * ∑ a, P j a *
          (α * nnorm (f (x a) - x a) + nnorm (x j - ∑ c, P j c • (x c + α • (f (x c) - x c)))) ≤
        (α + η) / s) ∧
    (∀ s : ℝ, 0 < s → s ≤ 1 →
      ∑ i, μ i * nnorm (x i - xbar P x s i) ≤ (α + η) / s ∧
      condVar P μ x s ≤ ∑ i, μ i * ∑ j, geo P s i j * nnorm (x j - x i) ^ 2 ∧
      ∑ i, μ i * ∑ j, geo P s i j * nnorm (x j - x i) ^ 2 =
        2 / (Fintype.card ι : ℝ) * ∑ i, μ i * ∑ j, geo P s i j * ∑ c, (x i c - x j c) * x i c ∧
      2 / (Fintype.card ι : ℝ) * ∑ i, μ i * ∑ j, geo P s i j * ∑ c, (x i c - x j c) * x i c =
        2 / (Fintype.card ι : ℝ) * ∑ i, μ i * ∑ c, (x i c - xbar P x s i c) * x i c ∧
      2 / (Fintype.card ι : ℝ) * ∑ i, μ i * ∑ c, (x i c - xbar P x s i c) * x i c ≤
        2 * ∑ i, μ i * nnorm (x i - xbar P x s i) ∧
      condVar P μ x s ≤ 2 * (α + η) / s) := by sorry

end CEPolytopeHard
