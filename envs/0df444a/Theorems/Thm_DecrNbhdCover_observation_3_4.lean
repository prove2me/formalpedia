-- Prove2me | Theorems.Thm_DecrNbhdCover_observation_3_4
-- name    : DecrNbhdCover.observation_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:33.708562+00:00
-- url     : https://prove2.me/theorems/38be28dc-6fa6-42e5-8ebe-37822d33fe21
-- title:
--   Observation 3.4 — Property P4 of $H_{G,\mathcal N}$
-- statement:
--   Let $\mathcal N$ be an $(\epsilon,d,D)$-shelled neighborhood cover for a graph $G$, for parameters $0<\epsilon<1$, $0<d<D$ with $D\ge d2^{32/\epsilon^c}$, for a large enough integral constant $c$, and let $H=H_{G,\mathcal N}$. Then $H$ has Property P4: for all $u,v\in V(G)$,
--   $$\mathrm{dist}_H(u,v)\ge\mathrm{dist}_G(u,v).$$
--
--   This is the non-contraction half of the emulator property.
--
--   Differences from the source:
--   - encoding: $0<\epsilon<1$ in the statement → the bounds on $\epsilon,d,D$, including $\epsilon<1/2$, are the fields of the shelled cover; reason: Definition 3.3 already requires $\epsilon<1/2$ and integers $d,D$; nothing is added
--   - reading: "a large enough constant $c$" → $\exists c_0\,\forall c\ge c_0$, with $c$ a parameter of the definitions and $C$ chosen after $c$; reason: $c$ is a universal constant, and the proof of Theorem 3.23 (p.24) chooses its $c$ "sufficiently larger than $c_0$"
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Observation 3.4, p.18 (PDF 22)

import Mathlib
import Definitions.Def_DecrNbhdCover_ShelledCover

set_option autoImplicit false

namespace DecrNbhdCover

open scoped ENNReal

/-- **Observation 3.4.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.18 (PDF 22).

"Let G be a graph, and let N be an (ϵ, d, D)-shelled neighborhood cover for G for some parameters 0 < ϵ < 1 and 0 < d < D, where D ≥ d · 2^(32/ϵ^c), for a large enough integral constant c. Let H = H_(G,N) be the graph derived from G and N. Then H has Property P4."

**Formalization Note.** The bounds on `ϵ`, `d` and `D` are fields of `IsShelledCover`. -/
theorem observation_3_4 :
    ∃ c₀ : ℕ, ∀ c, c₀ ≤ c →
      ∀ {α σ ε : Type} (G : Graph α ε) (N : ShelledCover α σ) (eps : ℝ) (d D : ℕ),
        G.WF → IsShelledCover G N eps d D c → P4 G (hGN G N eps d c) := by sorry

end DecrNbhdCover
