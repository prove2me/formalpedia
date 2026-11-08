-- Prove2me | Theorems.Thm_DecrNbhdCover_corollary_3_8
-- name    : DecrNbhdCover.corollary_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:07.276031+00:00
-- url     : https://prove2.me/theorems/4ad42433-243e-41bd-ba37-bf973bfcc78e
-- title:
--   Corollary 3.8 — $H_{G,\mathcal N}$ is a proper $(\epsilon',d,D)$-emulator for every $\epsilon+\epsilon^2/2\le\epsilon'<1$
-- statement:
--   Let $\mathcal N$ be an $(\epsilon,d,D)$-shelled neighborhood cover for a static graph $G$, for parameters $0<\epsilon<1$, $0<d<D$ with $D\ge d2^{32/\epsilon^c}$, for a large enough integral constant $c$, and let $H=H_{G,\mathcal N}$. Then for every $\epsilon'$ with
--   $$\epsilon+\frac{\epsilon^2}{2}\le\epsilon'<1,$$
--   the graph $H$ is a proper $(\epsilon',d,D)$-emulator for $G$.
--
--   This is how every emulator of the construction is certified.
--
--   Differences from the source:
--   - encoding: $0<\epsilon<1$ in the statement → the bounds on $\epsilon,d,D$, including $\epsilon<1/2$, are the fields of the shelled cover; reason: Definition 3.3 already requires $\epsilon<1/2$ and integers $d,D$; nothing is added
--   - reading: "a large enough constant $c$" → $\exists c_0\,\forall c\ge c_0$, with $c$ a parameter of the definitions and $C$ chosen after $c$; reason: $c$ is a universal constant, and the proof of Theorem 3.23 (p.24) chooses its $c$ "sufficiently larger than $c_0$"
--   - reading: "every path $P$" in Property Q1 → every simple path; reason: $P[v,a]$ and "$a\in V(P)\setminus\{v\}$" are used for simple paths: the proof in C.2 takes "the vertex that lies furthest from $v$ on $P$", and on a walk returning to $v$ its choice of $a$ can equal $v$
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Corollary 3.8, p.19 (PDF 23)

import Mathlib
import Definitions.Def_DecrNbhdCover_ShelledCover

set_option autoImplicit false

namespace DecrNbhdCover

open scoped ENNReal

/-- **Corollary 3.8.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.19 (PDF 23).

"Let G be a (static) graph, and let N be an (ϵ, d, D)-shelled neighborhood cover for G for some parameters 0 < ϵ < 1 and 0 < d < D, where D ≥ d · 2^(32/ϵ^c), for a large enough integral constant c. Let H = H_(G,N) be the graph derived from G and N. Then, for every ϵ′ with ϵ + ϵ²/2 ≤ ϵ′ < 1, graph H is a proper (ϵ′, d, D)-emulator for G."

**Formalization Note.** The bounds on `ϵ`, `d` and `D` are fields of `IsShelledCover`. -/
theorem corollary_3_8 :
    ∃ c₀ : ℕ, ∀ c, c₀ ≤ c →
      ∀ {α σ ε : Type} (G : Graph α ε) (N : ShelledCover α σ) (eps eps' : ℝ) (d D : ℕ),
        G.WF → IsShelledCover G N eps d D c → eps + eps ^ 2 / 2 ≤ eps' → eps' < 1 →
        IsProper G (hGN G N eps d c) eps' d (D : ℝ) := by sorry

end DecrNbhdCover
