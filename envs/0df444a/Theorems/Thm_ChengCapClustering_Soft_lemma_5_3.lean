-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_5_3
-- name    : ChengCapClustering.Soft.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:24.60803+00:00
-- url     : https://prove2.me/theorems/0e8e5914-8099-479c-a320-1a1453760596
-- title:
--   Lemma 5.3 — nearly optimal centers give $(u+\frac{z-1}{z}\omega,\ v+\frac{\omega}{z})$-movability, $\omega=C_z|g|\eta^\alpha$; optimal centers give $(u,v)$
-- statement:
--   Let $z>1$ and $\alpha=\min\{(z-1)/z,1/2\}$. There is a constant $C_z$ depending only on $z$ such that for every $z$-certificate $(u,g,v)$: if $Q$ is a multiset of $w$ points of $\mathbb R^d$ and $a\in\mathbb R^d$ satisfies $\Psi_Q(a)\le(1+\eta)\min_c\Psi_Q(c)$ with $\eta\in[0,1]$, then for all $y_1,\dots,y_w\in\mathbb R^d$ some bijection $\varphi$ satisfies $\sum_{p\in Q}\|p-y_{\varphi(p)}\|^z\le(u+\frac{z-1}{z}\omega)\Psi_Q(a)+(v+\frac{\omega}{z})\sum_{p\in Q}\|a-y_{\varphi(p)}\|^z$ with $\omega=C_z|g|\eta^\alpha$. In particular, a block whose representative is an optimal center of the block is $(u,v)$-movable.
--
--   Differences from the source:
--   - encoding: a multiset Q of w points; min over c of Ψ_Q(c) → an indexed family q : Fin w → ℝ^d; the real infimum ⨅ c, Ψ_Q(c) (nonempty index, bounded below by 0, attained); reason: listing with multiplicity; the infimum is the minimum
--   - encoding: "a block whose representative is an optimal center is (u, v)-movable" → IsMovable z u v with slots anywhere in ℝ^d (F = ℝ^d) for every a minimizing Ψ_Q; reason: the Euclidean setting of §5.3 has F = ℝ^d
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 5.3, printed p. 27 / PDF p. 29

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Clustering
import Definitions.Def_ChengCapClustering_Soft_Certificate

namespace ChengCapClustering.Soft

/-- Lemma 5.3 (Nearly optimal centers), printed p. 27 / PDF p. 29. For `z > 1` there is a constant
`C_z` (depending only on `z`) such that for every `z`-certificate `(u, g, v)`, with
`α = min{(z − 1)/z, 1/2}`: if `Q` is a multiset of `w` points of `ℝ^d` and `Ψ_Q(a) ≤ (1 + η) min_c Ψ_Q(c)`
with `η ∈ [0, 1]`, then for all `y_1, …, y_w ∈ ℝ^d` some bijection `φ` satisfies
`∑_p ‖p − y_{φ(p)}‖^z ≤ (u + (z−1)ω/z) Ψ_Q(a) + (v + ω/z) ∑_p ‖a − y_{φ(p)}‖^z`, `ω = C_z |g| η^α`.
In particular, a block whose representative is an optimal center of the block is `(u, v)`-movable. -/
theorem lemma_5_3 (z : ℝ) (hz : 1 < z) :
    ∃ Cz : ℝ, ∀ u g v : ℝ, IsCertificate z u g v →
      (∀ (d w : ℕ) (q : Fin w → Euc d) (a : Euc d) (η : ℝ), 0 ≤ η → η ≤ 1 →
        psi z Finset.univ q a ≤ (1 + η) * ⨅ c : Euc d, psi z Finset.univ q c →
        ∀ y : Fin w → Euc d, ∃ φ : Fin w ≃ Fin w,
          ∑ i, ‖q i - y (φ i)‖ ^ z ≤
            (u + (z - 1) / z * (Cz * |g| * η ^ min ((z - 1) / z) (1 / 2))) *
                psi z Finset.univ q a +
              (v + Cz * |g| * η ^ min ((z - 1) / z) (1 / 2) / z) *
                ∑ i, ‖a - y (φ i)‖ ^ z) ∧
      ∀ (d w : ℕ) (q : Fin w → Euc d) (a : Euc d),
        (∀ c : Euc d, psi z Finset.univ q a ≤ psi z Finset.univ q c) →
        IsMovable z u v Set.univ (Finset.univ : Finset (Fin w)) q a := by sorry

end ChengCapClustering.Soft
