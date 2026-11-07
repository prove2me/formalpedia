-- Prove2me | Theorems.Thm_BeatingGV42_theorem_1_1
-- name    : BeatingGV42.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:11.929943+00:00
-- url     : https://prove2.me/theorems/9580254a-7fe0-4cc8-8f55-da02cba5b573
-- title:
--   Theorem 1.1 — for a universal $\beta>0$ and every $\delta\in[0.39,0.48]$, 42-ary code families with relative distance $\ge\delta$ and rate $\ge1-H_{42}(\delta)+\beta$
-- statement:
--   There is a universal constant $\beta>0$ such that for every $\delta\in[0.39,0.48]$ there is a family of codes over an alphabet of size $42$, of lengths tending to infinity, with asymptotic relative distance at least $\delta$ and asymptotic rate at least
--   $$
--   1-H_{42}(\delta)+\beta .
--   $$
--   That is, the Gilbert–Varshamov bound $1-H_{42}(\delta)$ is beaten by a fixed margin on the whole interval $[0.39,0.48]$ at alphabet size 42, lowering the threshold of Zinoviev and Litsyn (46).
--
--   **Formalization Note** One $\beta>0$ is chosen before $\delta$. The alphabet is `Fin 42`; `HasCodeFamily 42 δ R` asks for lengths $n_i\to\infty$, every code of minimum distance $\ge\delta n_i$, and $\liminf_i\log_{42}|C_i|/n_i\ge R$ in $\varepsilon$-form; $H_{42}$ is in base $42$.
--
--   Differences from the source:
--   - generalization: asymptotic relative distance at least δ: liminf d(C_i)/n_i ≥ δ → every code C_i has minimum distance ≥ δ n_i; reason: pointwise implies the liminf form; Proposition 4.9's proof delivers it (4.20)
--   - encoding: asymptotic rate at least 1 − H_42(δ) + β → ∀ ε > 0, eventually 1 − H_42(δ) + β − ε ≤ log_42 |C_i| / n_i; reason: equivalent to liminf ≥ 1 − H_42(δ) + β; avoids Filter.liminf junk
--   - encoding: a family of codes over an alphabet of size 42 → n : ℕ → ℕ with Tendsto n atTop atTop and C i : Finset (Fin (n i) → Fin 42); reason: any alphabet of size 42 is in bijection with Fin 42; families have lengths → ∞ as in Proposition 4.9
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Theorem 1.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_BeatingGV42_Hq
import Definitions.Def_BeatingGV42_HasCodeFamily

set_option autoImplicit false

namespace BeatingGV42

/-- **Theorem 1.1** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), p.3 (PDF p.5)): "There exists a universal constant β > 0 such that, for
every δ ∈ [0.39, 0.48], there exists a family of codes over an alphabet of size 42 with asymptotic
relative distance at least δ and asymptotic rate at least 1 − H_42(δ) + β."

**Formalization Note** One `β > 0` is chosen before `δ`. The alphabet is `Fin 42`. A family of codes
(`HasCodeFamily`) has lengths `n_i → ∞`, every code of minimum distance at least `δ n_i` (pointwise
in `i`), and `liminf_i log_42 |C_i|/n_i ≥ 1 − H_42(δ) + β` in the `ε`-form. `H_42` is in base 42
(`Hq 42 δ = qaryEntropy 42 δ / ln 42`). -/
theorem theorem_1_1 :
    ∃ β : ℝ, 0 < β ∧ ∀ δ ∈ Set.Icc (39 / 100 : ℝ) (48 / 100),
      HasCodeFamily 42 δ (1 - Hq 42 δ + β) := by sorry

end BeatingGV42
