-- Prove2me | Theorems.Thm_BipColorHard_lemma_13
-- name    : BipColorHard.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:53.356302+00:00
-- url     : https://prove2.me/theorems/0a90088a-98c5-4481-a278-285e70cd3b29
-- title:
--   Lemma 13 — the gadget
-- statement:
--   Let $q=2k+1\ge3$ with $D$ as above. There is a fixed $\gamma\ne0$ with $-1/(k+1)<\gamma<1/k$ such that, for every integer $r\ge1$ and $\delta>0$, there is a simple bipartite graph $R$ of maximum degree at most $D$, with $r$ distinct ordered ports on its left side, each of degree at most $D-1$, satisfying
--   $$e^{-\delta}\nu_r\le\mu_R\le e^{\delta}\nu_r\quad\text{pointwise on }[q]^r.$$
--
--   Replacing each vertex of a phase labeling instance by a copy of $R$ realizes the labels through colorings.
--
--   Differences from the source:
--   - encoding: a simple bipartite graph with left and right sides → `SimpleGraph (Fin N)` with a map `side` to `Bool`, proper on edges, `true` being the left side; reason: §3: a fixed partition is part of a bipartite graph
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 13, p.13 (PDF p.15); (15) and the definition of a port, p.12 (PDF p.14)

import Definitions.Def_BipColorHard_Hardness
import Definitions.Def_BipColorHard_Gadget

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 13**, p.13 (PDF p.15), manuscript sha256 78a66d1f…, for `q = 2k + 1 ≥ 3`, `D` of §3. There is a fixed `γ ≠ 0` as in (15)
(`-1/(k+1) < γ < 1/k`) such that, for every integer `r ≥ 1` and `δ > 0`, there is a simple bipartite graph `R` of maximum degree
at most `D`, with `r` distinct ordered ports on its left side, satisfying `e^{-δ} ν_r ≤ μ_R ≤ e^{δ} ν_r` pointwise on `[q]^r`.

**Formalization Note.** A port is "a designated vertex of degree at most `D - 1`, so one more edge can be attached to it" (p.12, PDF
p.14). `side` is the fixed bipartition, with `true` the left side. -/
theorem lemma_13 (k : ℕ) (hk : 1 ≤ k) :
    ∃ γ : ℝ, γ ≠ 0 ∧ -(1 / ((k : ℝ) + 1)) < γ ∧ γ < 1 / (k : ℝ) ∧
      ∀ (r : ℕ), 1 ≤ r → ∀ δ : ℝ, 0 < δ →
        ∃ (N : ℕ) (R : SimpleGraph (Fin N)) (side : Fin N → Bool) (port : Fin r → Fin N),
          (∀ x y, R.Adj x y → side x ≠ side y) ∧
          (∀ v, (R.neighborSet v).ncard ≤ bipDeg (2 * k + 1)) ∧
          Function.Injective port ∧
          (∀ i, side (port i) = true) ∧
          (∀ i, (R.neighborSet (port i)).ncard + 1 ≤ bipDeg (2 * k + 1)) ∧
          ∀ τ : Fin r → Fin (2 * k + 1),
            Real.exp (-δ) * nuR γ τ ≤ muPorts R port τ ∧
              muPorts R port τ ≤ Real.exp δ * nuR γ τ := by sorry

end BipColorHard
