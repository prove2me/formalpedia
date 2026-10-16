-- Prove2me | Theorems.Thm_AcquihiringMonopsony_PrivateInfo_proposition_5
-- name    : AcquihiringMonopsony.PrivateInfo.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:56.73105+00:00
-- url     : https://prove2.me/theorems/b47db36f-54bf-4212-a5e9-5b1b27dee80e
-- title:
--   Proposition 5 — acquihiring if v_a > v_s + (7−3√5)B/2, else direct hiring with poaching probability (v_a−v_s+B)/(3B); the employee prefers direct hiring
-- statement:
--   Consider the private-benefit model of §6: an employee produces $v_a$ at an acquirer and $v_s$ at a startup, enjoys a private benefit $b \sim U[0,B]$ at the startup that only she observes, and has an outside option worth $0$, with
--   $$0 < B < \min\{v_a,v_s\}, \qquad v_s - B < v_a < v_s + 2B .$$
--   The acquirer chooses between **acquihiring** (buying the startup, then hiring her; its profit is $\max\{0, v_a - v_s\}$ by Lemma 2 with wage floor $0$) and **direct hiring** (a simultaneous wage game with the startup, played at Lemma 5's equilibrium wages $w_a^* = (2v_a+v_s-B)/3$, $w_s^* = (2v_s+v_a-2B)/3$). Let
--   $$\hat v_a = v_s + \frac{7-3\sqrt5}{2}\,B .$$
--   Then:
--
--   1. $\hat v_a > v_s$;
--   2. $(w_a^*, w_s^*)$ is an equilibrium of the direct-hiring wage game;
--   3. if $v_a > \hat v_a$, the acquirer's expected profit under direct hiring is strictly below its acquihiring profit, so it engages in acquihiring;
--   4. if $v_a < \hat v_a$, the direct-hiring profit is strictly above the acquihiring profit, so it engages in direct hiring, and it poaches the employee with probability
--   $$\frac{v_a - v_s + B}{3B};$$
--   5. the employee always prefers direct hiring: for every type $b \in [0,B]$ her payoff under acquihiring is strictly below her payoff $\max\{w_a^*, w_s^* + b, 0\}$ under direct hiring.
--
--   The result shows that private information softens wage competition enough that acquihiring is no longer always chosen, while the employee is still worse off whenever it is.
--
--   **Formalization Note** The direct-hiring branch is evaluated at Lemma 5's equilibrium wages, the continuation equilibrium the paper uses; the statement does not claim this equilibrium is unique. The acquihiring profit and the employee's acquihiring payoff are Lemma 2's outcomes with wage floor $0$, which the paper invokes in §6 and which the milestone on the monopsonistic wage supports. At $v_a = v_s$ (inside the direct-hiring branch) the acquisition is taken to fail, so the employee keeps $b$; either outcome of that tie is below her direct-hiring payoff. Clause 5 is pointwise in the type, which is the paper's "she earns a strictly positive wage and may receive a private benefit".
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), pp. 16–17 (PDF 17–18), Proposition 5 and its proof

import Mathlib
import Definitions.Def_AcquihiringMonopsony_PrivateInfo_Model

namespace AcquihiringMonopsony.PrivateInfo

theorem proposition_5 (P : Params) (hP : P.Standing) :
    P.vs < vHat P ∧
    IsDHEquilibrium P (waStar P) (wsStar P) ∧
    (vHat P < P.va → profitA P (waStar P) (wsStar P) < ahProfitA P) ∧
    (P.va < vHat P → ahProfitA P < profitA P (waStar P) (wsStar P) ∧
      poachProb P (waStar P) (wsStar P) = (P.va - P.vs + P.B) / (3 * P.B)) ∧
    (∀ b ∈ Set.Icc (0:ℝ) P.B, ahPayoffE P b < dhPayoffE (waStar P) (wsStar P) b) := by sorry

end AcquihiringMonopsony.PrivateInfo
