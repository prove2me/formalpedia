-- Prove2me | Theorems.Thm_DaiWeissFluid_KellyType_drift_identity
-- name    : DaiWeissFluid.KellyType.drift_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:06:12.997976+00:00
-- url     : https://prove2.me/theorems/a605bdbf-4689-4c40-83a5-a485709b7ef9
-- title:
--   Proof of Theorem 6.1 — drift identity Gᵢ(t) = Gᵢ(0) + |Cᵢ|t − Bᵢ(t)/βᵢ in a Kelly-type line
-- statement:
--   Let a reentrant line be of Kelly type with station means $\beta_1,\dots,\beta_I$ (so $m_k = \beta_{\sigma(k)}$), with all $m_k > 0$, and let $(Q,T)$ be a fluid model solution of (1.8)–(1.12). For a station $i$ put $G_i(t) = \sum_{k\in C_i} Q_k^+(t)$ with $Q_k^+(t) = \sum_{l \le k} Q_l(t)$. Then for every $t \ge 0$
--
--   $$ G_i(t) = G_i(0) + |C_i|\,t - \frac{1}{\beta_i} B_i(t), $$
--
--   where $B_i(t) = \sum_{k \in C_i} T_k(t)$ is the cumulative busy time of station $i$.
--
--   For a two-station line without immediate feedback, with $K = 2n$ classes and the route starting at station 1, $|C_1| = |C_2| = n$, and this is the paper's pair of displays $G_1(t) = G_1(0) + nt - (1/\beta_1)B_1(t)$, $G_2(t) = G_2(0) + nt - (1/\beta_2)B_2(t)$. The identity converts the queue dynamics into a statement about busy time alone, which is what makes the drift of $G_i$ computable.
--
--   **Formalization Note** The paper's second display prints "$G_2(t) = G_2(t) + nt - (1/\beta_2)B_2(t)$"; the intended reading, from (1.8) and the first display, is $G_2(0) + nt - \dots$, which is what is stated. The identity is stated for any number of stations and classes and any Kelly-type line, which implies the printed $K = 2n$ form. Indices are 0-based.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 130, proof of Theorem 6.1 (displays defining G₁, G₂)

import Mathlib
import Definitions.Def_DaiWeissFluid_KellyType_FluidModel
import Definitions.Def_DaiWeissFluid_KellyType_KellyLine

namespace DaiWeissFluid.KellyType

/-- Proof of Theorem 6.1, p. 130 (the displays defining `G₁`, `G₂`), in general form: for a
Kelly-type reentrant line with station means `β`, along every fluid solution and for `t ≥ 0`,
`G_i(t) = ∑_{k ∈ C_i} Q_k⁺(t)` satisfies `G_i(t) = G_i(0) + |C_i| t - B_i(t)/β_i`. For a
two-station line with `K = 2n` alternating classes this is the printed
`G_i(t) = G_i(0) + nt - (1/β_i)B_i(t)`. -/
theorem drift_identity {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (β : Fin I → ℝ) (hkelly : L.IsKellyType β)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsFluidSolution Q T) (i : Fin I) (t : ℝ) (ht : 0 ≤ t) :
    L.kellyG Q i t = L.kellyG Q i 0 + ((L.C i).card : ℝ) * t - L.busy T i t / β i := by sorry

end DaiWeissFluid.KellyType
