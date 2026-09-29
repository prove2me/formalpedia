-- Prove2me | Theorems.Thm_BanditAlgorithm_kiefer_wolfowitz_equivalence
-- name    : BanditAlgorithm.kiefer_wolfowitz_equivalence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T02:58:00.26256+00:00
-- url     : https://prove2.me/theorems/1832c77e-9e4b-4067-8dc3-cb5863ff19e0
-- statement:
--   (Kiefer–Wolfowitz; L&S Theorem 21.1) Let $\mathcal{A} \subseteq \mathbb{R}^d$ ($d \ge 1$) be compact with $\operatorname{span}(\mathcal{A}) = \mathbb{R}^d$. A design is a probability measure $\pi$ supported in $\mathcal{A}$, with moment matrix and G-objective
--
--   $$V(\pi) = \int a\,a^\top\,d\pi(a), \qquad g(\pi) = \sup_{a\in\mathcal{A}} \|a\|^2_{V(\pi)^{-1}}.$$
--
--   For every design $\pi^*$, the following are equivalent:
--
--   - (a) $\pi^*$ is G-optimal ($V(\pi^*)$ positive definite and $\pi^*$ minimizes $g$ among designs with positive-definite moment matrix);
--   - (b) $\pi^*$ maximizes $\det V(\pi)$ over all designs (equivalently, maximizes $\log \det V(\pi)$);
--   - (c) $g(\pi^*) = d$.
--
--   Moreover there exists a G-optimal design supported on a finite set of at most $d(d+1)/2$ points.
-- source:
--   L&S Theorem 21.1, p.268

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_SelfNormalizedProcess


open MeasureTheory Matrix

theorem BanditAlgorithm.kiefer_wolfowitz_equivalence
    {d : ℕ} (hd : 0 < d) (𝒜 : Set (Fin d → ℝ)) (h𝒜 : IsCompact 𝒜)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) :
    (∀ πs : Measure (Fin d → ℝ), IsDesignOn d 𝒜 πs →
      ((IsGOptimalDesign d 𝒜 πs ↔
          ∀ π : Measure (Fin d → ℝ), IsDesignOn d 𝒜 π →
            (designMatrix d π).det ≤ (designMatrix d πs).det) ∧
        (IsGOptimalDesign d 𝒜 πs ↔ designGValue d 𝒜 πs = (d : ℝ)))) ∧
    ∃ πs : Measure (Fin d → ℝ), IsDesignOn d 𝒜 πs ∧ IsGOptimalDesign d 𝒜 πs ∧
      ∃ s : Finset (Fin d → ℝ), ↑s ⊆ 𝒜 ∧ s.card ≤ d * (d + 1) / 2 ∧
        πs ((↑s : Set (Fin d → ℝ))ᶜ) = 0 := by
  sorry
