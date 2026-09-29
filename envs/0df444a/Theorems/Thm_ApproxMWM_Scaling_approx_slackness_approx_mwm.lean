-- Prove2me | Theorems.Thm_ApproxMWM_Scaling_approx_slackness_approx_mwm
-- name    : ApproxMWM.Scaling.approx_slackness_approx_mwm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:07:31.049317+00:00
-- url     : https://prove2.me/theorems/f66c2107-b38c-4b18-aeba-7d631d9a1e42
-- title:
--   Lemma 2.3 — approximate complementary slackness gives a $(1+\epsilon_1)^{-1}(1-\epsilon_0)$-MWM
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with real edge weights $w$, let $M$ be a matching, and let $\Omega$ be a laminar set of full blossoms with respect to $M$. Let $y:V\to\mathbb R$ and $z$ (on vertex sets) be dual values satisfying Property 2.2(1,2):
--
--   1. $z(B)\ge0$ for every odd set $B$, $y(u)\ge0$ for every vertex $u$, and $y(u)>0$ only if $u$ is matched;
--   2. every odd set $B$ with $z(B)>0$ belongs to $\Omega$, and every root blossom $B$ of $\Omega$ has $z(B)>0$.
--
--   Suppose domination and tightness hold approximately: $yz(e)\ge(1-\epsilon_0)w(e)$ for every edge $e$, and $yz(e)\le(1+\epsilon_1)w(e)$ for every $e\in M\cup\bigcup_{B\in\Omega}E_B$. If the $y$-values of free vertices are zero, then for every matching $M'$ of $G$
--   $$w(M)\ \ge\ (1+\epsilon_1)^{-1}(1-\epsilon_0)\,w(M'),$$
--   that is, $M$ is a $\big((1+\epsilon_1)^{-1}(1-\epsilon_0)\big)$-MWM.
--
--   This is the bridge from the relaxed dual conditions maintained by the scaling algorithm to an approximation guarantee for its output.
--
--   **Formalization Note** The paper does not bound $\epsilon_0,\epsilon_1$; the statement assumes only $\epsilon_1>-1$, so that $(1+\epsilon_1)^{-1}$ is positive. The comparison with "any maximum weight matching $M^*$" is stated for every matching $M'$, which needs no existence of a maximizer.
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, pp. 1:11–1:12, Lemma 2.3 (with Property 2.2, p. 1:11)

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Matching

namespace ApproxMWM.Scaling

/-- Lemma 2.3 (Duan–Pettie, J. ACM 61(1) 2014, pp. 1:11–1:12). Let `M` be a matching of `G`, `Ω` a
laminar set of full blossoms with respect to `M` (edge sets `EB`), and `y`, `z` dual values
satisfying Property 2.2(1,2): nonnegativity (`z(B) ≥ 0` on odd sets, `y ≥ 0`, `y(u) > 0` only at
matched `u`) and active blossoms (`z(B) > 0` only for `B ∈ Ω`, every root blossom has
`z(B) > 0`); approximate domination `yz(e) ≥ (1 - ε₀) w(e)` on every edge; approximate tightness
`yz(e) ≤ (1 + ε₁) w(e)` on `M ∪ ⋃_{B ∈ Ω} E_B`; and zero `y` on free vertices. Then `M` is a
`(1 + ε₁)⁻¹ (1 - ε₀)`-MWM. The page does not bound `ε₀, ε₁`; the only range used is
`1 + ε₁ > 0`. -/
theorem approx_slackness_approx_mwm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (M : Finset (Sym2 V)) (Ω : Finset (Finset V))
    (EB : Finset V → Finset (Sym2 V)) (y : V → ℝ) (z : Finset V → ℝ) (ε₀ ε₁ : ℝ)
    (hε₁ : -1 < ε₁)
    (hM : IsMatching G M) (hΩ : IsBlossomFamily G M Ω EB)
    (hz_nonneg : ∀ B : Finset V, Odd B.card → 0 ≤ z B)
    (hy_nonneg : ∀ u : V, 0 ≤ y u)
    (hy_matched : ∀ u : V, 0 < y u → IsMatched M u)
    (hz_active : ∀ B : Finset V, Odd B.card → 0 < z B → B ∈ Ω)
    (hz_root : ∀ B : Finset V, IsRoot Ω B → 0 < z B)
    (hdom : ∀ e ∈ G.edgeSet, (1 - ε₀) * w e ≤ yz y z e)
    (htight : ∀ e ∈ G.edgeSet, (e ∈ M ∨ ∃ B ∈ Ω, e ∈ EB B) → yz y z e ≤ (1 + ε₁) * w e)
    (hfree : ∀ u : V, IsFree M u → y u = 0) :
    IsApproxMWM G w ((1 + ε₁)⁻¹ * (1 - ε₀)) M := by sorry

end ApproxMWM.Scaling
