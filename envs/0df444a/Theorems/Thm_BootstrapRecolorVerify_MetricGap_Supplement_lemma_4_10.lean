-- Prove2me | Theorems.Thm_BootstrapRecolorVerify_MetricGap_Supplement_lemma_4_10
-- name    : BootstrapRecolorVerify.MetricGap.Supplement.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:32:50.378677+00:00
-- url     : https://prove2.me/theorems/c486c984-c6bf-40f3-8e2f-c6cc4c4be062
-- title:
--   Lemma 4.10 — Exact internal-edge radius estimate
-- statement:
--   For every fixed integer $r\ge2$ and every sufficiently large even $n$, let the Part I history satisfy the cloud-expansion and local-sparsity properties of §4.1. For every $2\le i\le r$, every collapsed coloring $\sigma:V(G_{i-1})\to V(G_i)$ and every level-$(i-1)$ cloud $U$ in $G_{i-1}$, let
--
--   $$R(U)=\min_{a\in U}\frac1{|U|}\sum_{b\in U}\rho_i(\sigma(a),\sigma(b)).$$
--
--   Then, with $\lambda_2^*=1/45$,
--
--   $$R(U)\le\frac2{\lambda_2^*}\underset{\substack{e=\{u,v\}\in E_{i-1}(G_{i-1})\\u,v\in U}}{\operatorname{Avg}}\rho_i(\sigma(u),\sigma(v))=90\underset{e\text{ internal to }U}{\operatorname{Avg}}\rho_i(\sigma(e_1),\sigma(e_2)).$$
--
--   The right average counts unordered internal edges once, retaining parallel multiplicity. The left minimization averages over every cloud vertex, including the center. Every such $\sigma$ is the collapse of a monochromatic map; no additional image-size restriction is imposed. This is the support for Theorem 4.9.
--
--   Differences from the source:
--   - encoding: fixed r≥2 and sufficiently large even n under the Part I construction → one threshold n₀(r)≥2 preceding every even n and every matching history; reason: this spells out the standing assumptions on pp.5–6 without excluding any sufficiently large even n
--   - encoding: the standing expansion and local-sparsity properties of §4 → GoodHistory, with expansion in its equivalent mean-zero Rayleigh form; reason: these are exactly Claims 4.2/4.5, without any embedding or radius conclusion
--   - encoding: 2≤i≤r, a collapsed coloring and a minimizing center → i=k+2, all maps σ on G_(i−1), and the infimum of the finite range of center averages; reason: every source stage and every collapsed map occurs; every such map lifts to a monochromatic input, and the nonempty finite infimum is its attained minimum
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), Lemma 4.10, p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=14; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Proxy

namespace BootstrapRecolorVerify.MetricGap.Supplement

/-- Lemma 4.10 p.14, with the two standing graph properties of §4.1.
The source index i=k+2 covers exactly 2≤i≤r. σ is any collapsed coloring;
its finite cloud domain already supplies the image-size bound. -/
theorem lemma_4_10 :
    ∀ r : ℕ, 2 ≤ r → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → Even n → ∀ H : History n r, GoodHistory H →
        ∀ k : ℕ, ∀ h : k + 2 ≤ r,
          ∀ σ : Vertex n (k + 1) → Vertex n (k + 2), ∀ u : Vertex n k,
            centerRadius r (historyPrefix n (k + 2) h H) σ u ≤
              90 * internalEdgeAverage r (historyPrefix n (k + 2) h H) σ u := by sorry

end BootstrapRecolorVerify.MetricGap.Supplement
