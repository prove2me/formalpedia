-- Prove2me | Theorems.Thm_CEPolytopeHard_eq_11
-- name    : CEPolytopeHard.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:52.760616+00:00
-- url     : https://prove2.me/theorems/013de2e2-8e8a-48a4-8e4a-6600cb823d65
-- title:
--   Section 3.2 — the bound $\gamma = (8t+\eta)/\alpha$ and Eq. (11)
-- statement:
--   Setting (one layer of Section 3.2): points $x_1, \dots, x_k \in [0,1]^d$, a stochastic matrix $P$ with stationary distribution $\mu$, a map $f$ of $[0,1]^d$ into itself, $\alpha \in (0, 1]$, $\Delta_j = f(x_j) - x_j$, $e_j = x_j - \sum_a P_{ja}(x_a + \alpha\Delta_a)$ (so that $x_j = \mathbb E_{a\sim P_j}[x_a + \alpha\Delta_a] + e_j$), and $\eta$ with $\mathbb E_{j\sim\mu}\|e_j\|_2 \le \eta$. Norms are normalized. In addition $f$ is $L$-Lipschitz on $[0,1]^d$ in the normalized norm with $L \ge 1$, and $0 < t \le 1/2$. Then
--
--   1. for every $i$,
--   $$
--   \Big\|\mathbb E_{j\sim P_i(t)}\Delta_j\Big\|_2 \le \frac{2t}{\alpha}\|x_i - \bar x_i(t)\|_2 + \frac1\alpha\,\mathbb E_{j\sim P_i(t)}\|e_j\|_2 + 2t\Big(\|\Delta_i\|_2 + \mathbb E_{j\sim P_i(t)}\|\Delta_j\|_2\Big) \le \frac{8t}\alpha + \frac1\alpha\,\mathbb E_{j\sim P_i(t)}\|e_j\|_2 ;
--   $$
--   2. $\mathbb E_{i\sim\mu}\big\|\mathbb E_{j\sim P_i(t)}\Delta_j\big\|_2 \le (8t + \eta)/\alpha =: \gamma$;
--   3. $\mathbb E_{i\sim\mu}\|\Delta_i\|_2 \le \gamma + 2L\sqrt{V(t)}$;
--   4. if moreover $t < s \le 1$, $r > 0$ and $h(t) - h(s) \le \log k / r$, then
--   $$
--   \gamma + 2L\sqrt{V(t)} \le \frac{8t + \eta}{\alpha} + 2L\sqrt{\frac{2\log k}{r} + \frac{2(\alpha+\eta)}{s}} .
--   $$
--
--   Clauses 3–4 are (11): at a good scale, the average residual $\|f(x_i) - x_i\|_2$ of the layer is small.
--
--   Differences from the source:
--   - generalization: the points of layer ℓ of a fixed set of the lift g, with P, µ from that fixed set, f the circuit map, α = α_ℓ and η = √r ϵ → arbitrary points in [0, 1]^d, any stochastic P with stationary µ, any f mapping [0, 1]^d into itself, any α ∈ (0, 1] and any η ≥ E_µ‖e_j‖₂; reason: the argument uses only these properties, and the layer data of Section 3.2 has them
--   - encoding: the layer choice s = t_{ℓ−1}, t = t_ℓ with h(t_ℓ) − h(t_{ℓ−1}) ≤ log k / r (p.16) → in clause 4, any s, r with t < s ≤ 1, r > 0 and h(t) − h(s) ≤ log k / r; reason: the layer choice enters (11) only through this inequality
--   - encoding: E_{j∼P_i(t),a∼P_j}‖e_j‖₂ and the other expectations → Σ_j P_ij(t)‖e_j‖₂ and finite weighted sums; reason: e_j does not depend on a and each row P_j sums to 1; same values
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 3.2, displays on pp.17–18 and Eq. (11), p.18

import Mathlib
import Definitions.Def_CEPolytopeHard_nnorm
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_CEPolytopeHard_geo
import Definitions.Def_CEPolytopeHard_condVar
import Definitions.Def_CEPolytopeHard_hEnt

set_option autoImplicit false

namespace CEPolytopeHard

/-- **The bound `γ` and the first inequality of Eq. (11)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Section 3.2, pp.17–18: "⃦E_{j∼P_i(t)} ∆_j⃦₂
≤ (2t/α)∥x_i − x̄_i(t)∥₂ + (1/α)E_{j∼P_i(t),a∼P_j}∥e_j∥₂ + 2t(∥∆_i∥₂ + E_{j∼P_i(t)}∥∆_j∥₂) ≤ 8t/α +
(1/α)E_{j∼P_i(t),a∼P_j}∥e_j∥₂. Averaging over i ∼ μ, we have E_{i∼μ}⃦E_{j∼P_i(t)} ∆_j⃦₂ ≤ (8t + η)/α =: γ"
and "Taking expectations over μ, using the fact that μ is stationary, and applying Jensen now
yields E_{i∼μ}∥∆_i∥₂ ≤ γ + 2L√V(t)").

Setting (Section 3.2, pp.16–17, for one layer): points `x_1, …, x_k ∈ [0, 1]^ι`, a stochastic matrix
`P` with stationary distribution `μ`, a map `f` of `[0, 1]^ι` into itself, `α ∈ (0, 1]`,
`Δ_j = f(x_j) − x_j`, `e_j = x_j − ∑_a P_{ja}(x_a + αΔ_a)` (so `x_j = E_{a∼P_j}[x_a + αΔ_a] + e_j`),
and `η` with `∑_j μ_j ‖e_j‖₂ ≤ η`. Norms are normalized (p.9), `D = card ι`.
In addition `f` is `L`-Lipschitz on `[0, 1]^ι` in the normalized norm with `L ≥ 1`, and
`0 < t ≤ 1/2`. Then
1. for every `i`, `‖E_{j∼P_i(t)} Δ_j‖₂` is at most the printed middle expression, which is at most
   `8t/α + (1/α) E_{j∼P_i(t)} ‖e_j‖₂`;
2. `E_{i∼μ} ‖E_{j∼P_i(t)} Δ_j‖₂ ≤ (8t + η)/α`;
3. `E_{i∼μ} ‖Δ_i‖₂ ≤ (8t + η)/α + 2L√V(t)`;
4. (second inequality of (11)) if moreover `t < s ≤ 1`, `r > 0` and `h(t) − h(s) ≤ log k / r` (the
   choice of the layer, p.16), then `(8t + η)/α + 2L√V(t) ≤ (8t + η)/α + 2L√(2 log k / r + 2(α + η)/s)`.

**Formalization Note** In clause 4 the layer choice of p.16 (`h(t_ℓ) − h(t_{ℓ−1}) ≤ log k / r`) is a
hypothesis on `t, s, r`. The points, the chain and `f` are arbitrary with the
properties the argument uses (the paper states it for one layer of a fixed set). -/
theorem eq_11 {k : ℕ} {ι : Type} [Fintype ι] (P : Matrix (Fin k) (Fin k) ℝ)
    (hP : IsStochastic P) (μ : Fin k → ℝ) (hμ : IsStationary P μ) (x : Fin k → ι → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ι → ℝ) 1) (f : (ι → ℝ) → ι → ℝ)
    (hf : ∀ y ∈ Set.Icc (0 : ι → ℝ) 1, f y ∈ Set.Icc (0 : ι → ℝ) 1) (L : ℝ) (hL : 1 ≤ L)
    (hlip : ∀ y ∈ Set.Icc (0 : ι → ℝ) 1, ∀ z ∈ Set.Icc (0 : ι → ℝ) 1,
      nnorm (f y - f z) ≤ L * nnorm (y - z))
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (η : ℝ)
    (hη : ∑ j, μ j * nnorm (x j - ∑ a, P j a • (x a + α • (f (x a) - x a))) ≤ η)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    (∀ i, nnorm (∑ j, geo P t i j • (f (x j) - x j)) ≤
        2 * t / α * nnorm (x i - xbar P x t i) +
          1 / α * ∑ j, geo P t i j * nnorm (x j - ∑ c, P j c • (x c + α • (f (x c) - x c))) +
          2 * t * (nnorm (f (x i) - x i) + ∑ j, geo P t i j * nnorm (f (x j) - x j)) ∧
      2 * t / α * nnorm (x i - xbar P x t i) +
          1 / α * ∑ j, geo P t i j * nnorm (x j - ∑ c, P j c • (x c + α • (f (x c) - x c))) +
          2 * t * (nnorm (f (x i) - x i) + ∑ j, geo P t i j * nnorm (f (x j) - x j)) ≤
        8 * t / α +
          1 / α * ∑ j, geo P t i j * nnorm (x j - ∑ c, P j c • (x c + α • (f (x c) - x c)))) ∧
    ∑ i, μ i * nnorm (∑ j, geo P t i j • (f (x j) - x j)) ≤ (8 * t + η) / α ∧
    ∑ i, μ i * nnorm (f (x i) - x i) ≤
      (8 * t + η) / α + 2 * L * Real.sqrt (condVar P μ x t) ∧
    ∀ s r : ℝ, t < s → s ≤ 1 → 0 < r → hEnt P μ t - hEnt P μ s ≤ Real.log k / r →
      (8 * t + η) / α + 2 * L * Real.sqrt (condVar P μ x t) ≤
        (8 * t + η) / α + 2 * L * Real.sqrt (2 * Real.log k / r + 2 * (α + η) / s) := by sorry

end CEPolytopeHard
