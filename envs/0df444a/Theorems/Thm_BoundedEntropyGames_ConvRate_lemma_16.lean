-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_lemma_16
-- name    : BoundedEntropyGames.ConvRate.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:41.494526+00:00
-- url     : https://prove2.me/theorems/0d064434-a70b-4288-97c5-bf128938613e
-- title:
--   Lemma 16, p. 20 — the degenerate cases: a pure action, or (18)–(21)
-- statement:
--   In the setting of (18)–(19), one of the following holds:
--
--   1. some pure action $a\in\mathcal A$ secures $J^{(A)}_{cav}(H(X|Y))$ in the stage game: $U^{(A)}(\delta_a)\ge J^{(A)}_{cav}(H(X|Y))$, where $\delta_a$ is the point mass at $a$;
--   2. there exist $r\in(0,1]$ and $p^{(1)}_A,p^{(2)}_A\in\Delta(\mathcal A)$ satisfying (18), (19) and $H(p^{(1)}_A)>H(p^{(2)}_A)$ (20).
--
--   In the first case Alice secures $J^{(A)}_{cav}(H(X|Y))$ in every stage by playing $a$, so Theorem 6 holds with $\mu=0$; in the second the block construction of §3.3 applies.
--
--   **Formalization Note** The paper states Lemma 16 as "Theorem 6 holds if Equations (20) and (21) fail to hold", a statement about the goal itself. Its proof (§3.3.1) establishes exactly this dichotomy, which is what is posed here.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 20, Lemma 16, (20)–(21); proof §3.3.1, pp. 24–25

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting

namespace BoundedEntropyGames.ConvRate

/-- Lemma 16, p. 20 (proof §3.3.1, pp. 24–25), as the dichotomy its proof establishes: either
a pure action secures `J_cav(H(X|Y))` in the stage game, or (18)–(19) hold together with
(20) `H(p^(1)) > H(p^(2))` and (21) `0 < r ≤ 1`. -/
theorem lemma_16 {𝒜 ℬ 𝒳 𝒴 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Nonempty 𝒜]
    [Fintype ℬ] [Nonempty ℬ] [Fintype 𝒳] [Fintype 𝒴]
    (u : 𝒜 → ℬ → ℝ) (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) :
    (∃ a : 𝒜, Jcav u (condEntropy pXY) ≤ U u (Pi.single a (1 : ℝ))) ∨
    ∃ r ∈ Set.Ioc (0 : ℝ) 1, ∃ p₁ ∈ stdSimplex ℝ 𝒜, ∃ p₂ ∈ stdSimplex ℝ 𝒜,
      r * U u p₁ + (1 - r) * U u p₂ = Jcav u (condEntropy pXY) ∧
      r * shannon p₁ + (1 - r) * shannon p₂ ≤ condEntropy pXY ∧
      shannon p₂ < shannon p₁ := by sorry

end BoundedEntropyGames.ConvRate
