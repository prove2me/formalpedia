-- Prove2me | Theorems.Thm_AcquihiringMonopsony_Bargaining_proposition_2
-- name    : AcquihiringMonopsony.Bargaining.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:49.414981+00:00
-- url     : https://prove2.me/theorems/4de6bf6f-37ce-43f5-9a93-6f55f0e5b849
-- title:
--   Proposition 2 — direct hiring if $v_a > \overline{v}_a$, acquihiring if $\underline{v}_a < v_a < \overline{v}_a$, no hiring if $v_a < \underline{v}_a$; the employee prefers direct hiring
-- statement:
--   Consider the bargaining extension of the acquihiring model. The employee generates value $v_a$ at the acquirer and $v_s$ at the startup, enjoys a private benefit $b$ at the startup, and earns at least the wage floor $\underline{w}$; the standing assumption is $b > 0$ and $\min\{v_a, v_s\} > b + \underline{w}$. The acquirer first chooses between **direct hiring** (a wage competition with the startup) and **acquihiring** (Nash bargaining over the startup's price, with acquirer bargaining power $\alpha$; after a failed bid the acquirer competes in wages with probability $\delta$). Let $0 < \alpha < 1$ and $0 < \delta < 1$, let $\sigma_D$ be any continuation equilibrium (in undominated strategies) of the direct-hiring subgame chosen at the first stage, and $\sigma_F$ any continuation equilibrium of the direct-hiring subgame played after a failed bid. Define
--
--   $$\overline{v}_a = v_s + b + \frac{\alpha}{(1-\alpha)(1-\delta)}\bigl[\delta(v_s - \underline{w}) + b\bigr], \qquad \underline{v}_a = \frac{v_s + \delta(\underline{w} + b)}{1+\delta}.$$
--
--   Then:
--
--   1. $\overline{v}_a > v_s + b$ and $\underline{v}_a < v_s$;
--   2. if $v_a > \overline{v}_a$, the acquirer strictly prefers direct hiring to acquihiring, and under direct hiring the employee joins the acquirer;
--   3. if $\underline{v}_a < v_a < \overline{v}_a$, the acquirer strictly prefers acquihiring to direct hiring, and the acquisition occurs;
--   4. if $v_a < \underline{v}_a$, no hiring occurs: the acquisition does not take place, and under direct hiring (at the first stage or after a failed bid) the employee stays at the startup;
--   5. the employee's expected payoff under acquihiring is strictly smaller than under direct hiring.
--
--   Proposition 2 is the main result of the bargaining extension: with bargaining over the price and a credible threat of wage competition after a failed bid, the acquirer may hire directly (for large $v_a$), and may acquihire even where the employee is more productive at the startup ($\underline{v}_a < v_a < v_s$).
--
--   **Formalization Note** The paper assumes "$0 < \alpha\delta < 1$", which allows $\alpha = 1$ or $\delta = 1$; there $(1-\alpha)(1-\delta) = 0$, $\overline{v}_a$ is undefined, and Lean's convention $x/0 = 0$ would make clause 2 false. The statement therefore assumes $0 < \alpha < 1$ and $0 < \delta < 1$, the range on which $\overline{v}_a$ is defined. The two direct-hiring equilibria $\sigma_D$ and $\sigma_F$ are separate hypotheses and are not assumed equal. The acquirer's choice is stated as a strict comparison of its expected payoffs under the two modes. Clause 5 covers a failed bid as well as an acquisition (the paper's proof treats the acquisition case), which holds because $\delta < 1$.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 9 (PDF 10), Proposition 2

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model
import Definitions.Def_AcquihiringMonopsony_Bargaining_NashSplit

namespace AcquihiringMonopsony.Bargaining

theorem proposition_2 (P : Baseline.Params) (hP : P.Standing) (α δ : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (σD σF : Baseline.DHProfile) (hD : Baseline.IsDHEquilibrium P σD)
    (hF : Baseline.IsDHEquilibrium P σF) :
    (P.vs + P.b < vUpper P α δ ∧ vLower P δ < P.vs) ∧
    (vUpper P α δ < P.va →
      ahPayoffA P α δ σF < Baseline.dhPayoffA P σD.acceptA σD.wa σD.ws ∧ σD.acceptA σD.wa σD.ws = true) ∧
    (vLower P δ < P.va → P.va < vUpper P α δ →
      Baseline.dhPayoffA P σD.acceptA σD.wa σD.ws < ahPayoffA P α δ σF ∧ AcquisitionOccurs P δ σF) ∧
    (P.va < vLower P δ →
      ¬ AcquisitionOccurs P δ σF ∧ σD.acceptA σD.wa σD.ws = false ∧
        σF.acceptA σF.wa σF.ws = false) ∧
    ahPayoffE P δ σF < Baseline.dhPayoffE P σD.acceptA σD.wa σD.ws := by sorry

end AcquihiringMonopsony.Bargaining
