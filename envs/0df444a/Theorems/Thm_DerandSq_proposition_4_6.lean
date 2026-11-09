-- Prove2me | Theorems.Thm_DerandSq_proposition_4_6
-- name    : DerandSq.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:08:52.416698+00:00
-- url     : https://prove2.me/theorems/a95c0241-51b2-4db7-a43a-4fbbedb7a3ff
-- title:
--   Proposition 4.6 — $\|Q_H(u)\| = \lim_p \tau(s^{2p})^{1/2p} = \lim_p (\#\text{closed walks of length } 2p \text{ at } e \text{ in } T_d\circledS H)^{1/2p}$
-- statement:
--   Let $d \geq 3$, let $H$ be a $k$-regular graph on $[d]$ with $k \geq 1$ (the standing assumptions of §4.2), and let $s = Q_H(u) \in C^*_{\mathrm{red}}(\Gamma_d)$ as in (4.10). Then
--   $$
--   \|s\|_{C^*_{\mathrm{red}}(\Gamma_d)} = \lim_{p \to \infty} \tau\bigl(s^{2p}\bigr)^{1/(2p)} = \lim_{p\to\infty} \Bigl[\text{number of closed walks in } T_d \circledS H \text{ of length } 2p \text{ originating at } e\Bigr]^{1/(2p)},
--   $$
--   where $\tau$ is the canonical trace of $C^*_{\mathrm{red}}(\Gamma_d)$ and $e \in \Gamma_d$ is the identity word. Both limits exist and equal the norm.
--
--   It reduces the norm of the limit object to a growth rate of closed walks in an explicit infinite graph.
--
--   Differences from the source:
--   - reading: ‖s‖ (s introduced only in Corollary 4.8 as s = Q_H(u)) → ‖QH H‖; reason: the statement's s is Q_H(u)
--   - encoding: ‖·‖_{C*_red(Γ_d)} → operator norm on ℓ²(Γ_d); reason: C*_red(Γ_d) is a C*-subalgebra of B(ℓ²(Γ_d)) with the operator norm
--   - encoding: τ(s^{2p})^{1/2p} → real part of τ(s^{2p}), raised to the real power 1/(2p); reason: s is self-adjoint, so τ(s^{2p}) = ‖s^p δ_e‖² is a nonnegative real
--   - encoding: closed walks in T_d Ⓢ H originating at e → closedWalks (dsTree H) 1 (2p), dsTree on Γ_d with right multiplication; reason: the paper's description of T_d Ⓢ H on p.22; Nat.card of a finite set of walks
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Proposition 4.6, p.22 (standing assumptions of §4.2, p.21)

import Mathlib
import Definitions.Def_DerandSq_tauRed
import Definitions.Def_DerandSq_QH
import Definitions.Def_DerandSq_dsTree
import Definitions.Def_DerandSq_closedWalks

namespace DerandSq

/-- Proposition 4.6 of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.22 (under §4.2's standing assumptions `d ≥ 3`, `H` `k`-regular,
`k ≥ 1`, p.21). For `s = Q_H(u) ∈ C*_red(Γ_d)` of (4.10),
`‖s‖_{C*_red(Γ_d)} = lim_{p → ∞} τ(s^{2p})^{1/(2p)}
  = lim_{p → ∞} [number of closed walks in T_d Ⓢ H of length 2p originating at e]^{1/(2p)}`.

**Formalization Note** `‖s‖_{C*_red(Γ_d)}` is the operator norm of `QH H` on `ℓ²(Γ_d)`; `τ` is
`tauRed`, whose value on `s^{2p}` is a nonnegative real, so its real part is taken; the walk count
is cast to `ℝ` before the real power. -/
theorem proposition_4_6 {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] (hH : H.IsRegularOfDegree k) :
    Filter.Tendsto (fun p : ℕ => (tauRed (QH H ^ (2 * p))).re ^ ((1 : ℝ) / (2 * p)))
        Filter.atTop (nhds ‖QH H‖) ∧
      Filter.Tendsto (fun p : ℕ => (closedWalks (dsTree H) 1 (2 * p) : ℝ) ^ ((1 : ℝ) / (2 * p)))
        Filter.atTop (nhds ‖QH H‖) := by sorry

end DerandSq
