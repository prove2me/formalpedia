-- Prove2me | Theorems.Thm_FirstOrderOpt_OperatorSliding_explicit_gs_rate
-- name    : FirstOrderOpt.OperatorSliding.explicit_gs_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:06:19.048617+00:00
-- url     : https://prove2.me/theorems/227c789a-0b33-4129-ae63-8f058cdf595c
-- title:
--   Corollary 8.1(a) — gradient sliding complexity, explicit constant
-- statement:
--   Continuing `gs_convergence_bound` (Theorem 8.1(a))'s setting, with the PS/GS schedule fully
--   instantiated.
--
--   **Corollary 8.1.** Assume $\{p_t\},\{\theta_t\}$ are set to $p_t = t/2$, $\theta_t =
--   2(t+1)/(t(t+3))$, $\forall t\ge1$ (8.1.39). (a) If $N$ is fixed a priori, and $\{\beta_k\},
--   \{\gamma_k\},\{T_k\}$ are set to
--   $$\beta_k = \frac{2L}{k}, \qquad \gamma_k = \frac{2}{k+1}, \qquad T_k =
--   \Big\lceil\frac{M^2Nk^2}{\tilde DL^2}\Big\rceil, \quad (8.1.40)$$
--   for some $\tilde D>0$, then
--   $$\Psi(\bar x_N)-\Psi(x^*) \le \frac{2L}{N(N+1)}\big[3V(x_0,x^*)+2\tilde D\big], \qquad
--   \forall N\ge1. \quad (8.1.41)$$
--
--   $\tilde D$ is a free parameter the algorithm's designer chooses to schedule the sliding length
--   $T_k$ (e.g. an estimate of $V(x_0,x^*)$); it is not intrinsic to the problem instance.
--
--   **Formalization Note.** `p_t=t/2` gives, via (8.1.44) (cited, not restated), the closed form
--   $P_t = 2/((t+1)(t+2))$ for every $t\ge0$ (including $P_0=1$), used directly (`hP`) rather than
--   the general recursion of (8.1.20), per the specific-instantiation convention (a closed form the
--   book's own corollary proof derives, not the general schedule). Likewise $\Gamma_k =
--   2/(k(k+1))$ for $k\ge1$ (8.1.46, `hΓ`). `hBd` is `gs_convergence_bound` (Theorem 8.1(a))'s
--   conclusion (8.1.34), specialized to this schedule and carried as a hypothesis — the goal's own
--   content is the algebraic simplification (8.1.45)-(8.1.48) of that bound into the closed form,
--   not the general theorem itself. The book's own printed $\beta_k=2L/(\nu k)$ in (8.1.40) is an
--   extraction artifact of the source text (there is no $\nu$-indexed quantity anywhere else in
--   this section); the proof's own line "$\gamma_k\beta_k/(\Gamma_k(1-P_{T_k})) = 2L/(1-P_{T_k})$"
--   is algebraically consistent only with $\beta_k=2L/k$, which is what `hβ` states.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 494, Corollary 8.1(a)

import Mathlib

namespace FirstOrderOpt.OperatorSliding

/-- Corollary 8.1(a) (gradient sliding complexity, explicit constant, `N` fixed a priori). `Ψ :=
f+h+chi` on the closed convex `X` (8.1.1), `x*` an optimal solution. `{p_t},{θ_t}` are set to
(8.1.39): `p_t = t/2`, which (via (8.1.44), cited not restated) gives the closed form `P_t =
2/((t+1)(t+2))` for every `t` (including `t=0`, matching `P_0=1`) and (via (8.1.46)) `Γ_k =
2/(k(k+1))` for `k≥1`. `{β_k},{γ_k},{T_k}` are set to (8.1.40): `β_k = 2L/k`, `γ_k = 2/(k+1)`,
`T_k = ⌈M²Nk²/(DtildeL²)⌉` for a designer-chosen `Dtilde>0` (a free parameter of the algorithm's schedule,
not derived from `X` or `f`). `hBd` is `gs_convergence_bound` (Theorem 8.1(a), this mission's other
milestone) applied with this schedule: `Ψ(xbar N)-Ψ(x*) ≤ Bd(N)`, the general (8.1.34) bound,
carried as a hypothesis rather than re-derived here. The goal is the algebraic simplification
(8.1.45)-(8.1.48) of `Bd(N)` under this schedule into the closed form (8.1.41).

**Formalization Note.** The book's own printed `βk = 2L/(νk)` (8.1.40) is an OCR/typesetting
artifact of the source text extraction; the proof's own line "`γkβk/(Γk(1−PTk)) = 2L/(1−PTk)`"
(p. 494/PDF 504, using `Γk=2/(k(k+1))` and `γk=2/(k+1)`) is consistent only with `βk = 2L/k`,
which is what is formalized here.

**Formalization Note (revised 2026-09-19).** `hM` tightened from `0 ≤ M` to `0 < M` per (8.1.3)'s
own "for some `L>0` and `M>0`". Load-bearing here (not merely cosmetic): together with `N ≥ 1`,
`Dtilde > 0`, `L > 0`, this makes `T k = ⌈M²Nk²/(Dtilde·L²)⌉₊` the ceiling of a strictly positive
real for every `k ≥ 1`, hence `T k ≥ 1` automatically — closing the same junk-value division
corner as `gs_convergence_bound`'s `hTpos` fix without needing a separate hypothesis here. -/
theorem explicit_gs_rate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h chi Ψ : E → ℝ) (hΨ : ∀ u, Ψ u = f u + h u + chi u)
    (V : E → E → ℝ) (hVnonneg : ∀ a b, 0 ≤ V a b)
    (L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X)
    (hxstarOpt : ∀ w ∈ X, Ψ xstar ≤ Ψ w)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ) (hDtilde : 0 < Dtilde)
    (p P Γ β γ : ℕ → ℝ) (T : ℕ → ℕ)
    (hp : ∀ t : ℕ, p t = (t : ℝ) / 2)
    (hP : ∀ t : ℕ, P t = 2 / (((t : ℝ) + 1) * ((t : ℝ) + 2)))
    (hΓ : ∀ k : ℕ, 1 ≤ k → Γ k = 2 / ((k : ℝ) * ((k : ℝ) + 1)))
    (hβ : ∀ k : ℕ, 1 ≤ k → β k = 2 * L / (k : ℝ))
    (hγ : ∀ k : ℕ, 1 ≤ k → γ k = 2 / ((k : ℝ) + 1))
    (hT : ∀ k : ℕ, 1 ≤ k → T k = ⌈M ^ 2 * (N : ℝ) * (k : ℝ) ^ 2 / (Dtilde * L ^ 2)⌉₊)
    (xbar : ℕ → E) (hxbar0 : xbar 0 = x0)
    (hBd : Ψ (xbar N) - Ψ xstar ≤
      Γ N * β 1 / (1 - P (T 1)) * V x0 xstar
        + M ^ 2 * Γ N / 2 *
            ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
              γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1))) :
    Ψ (xbar N) - Ψ xstar ≤ 2 * L / ((N : ℝ) * ((N : ℝ) + 1)) * (3 * V x0 xstar + 2 * Dtilde) := by sorry

end FirstOrderOpt.OperatorSliding
