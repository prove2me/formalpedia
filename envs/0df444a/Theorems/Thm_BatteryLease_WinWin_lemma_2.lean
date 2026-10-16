-- Prove2me | Theorems.Thm_BatteryLease_WinWin_lemma_2
-- name    : BatteryLease.WinWin.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:20:22.98602+00:00
-- url     : https://prove2.me/theorems/5fe3c44b-474f-4609-bc1c-1a7713868d4e
-- title:
--   Lemma 2, p. 13 — peak upgrade and downgrade volumes (interior cases with r_h in place of a)
-- statement:
--   Under the standing assumptions, fix a primary lease rate $p_h$, rates $\bar p_h,\bar p_l$ and a low-capacity lease volume $\tau\in[0,1]$. The peak upgrade volume $U$ (low lessees with $(D-r_h)^++\bar p_h\le D$) and downgrade volume $V$ (high lessees with $(D-r_h)^++p_h>D+\bar p_l$) satisfy:
--   1. if $\bar p_h<0$, then $U=\tau$; if $0\le\bar p_h\le r_h$, then $U=\tau(a-\bar p_h)/a$; if $\bar p_h>r_h$, then $U=0$ (in particular when $\bar p_h>a$);
--   2. if $\bar p_l<p_h-r_h$, then $V=1-\tau$ (in particular when $\bar p_l<p_h-a$); if $p_h-r_h\le\bar p_l\le p_h$, then $V=(1-\tau)(p_h-\bar p_l)/a$; if $\bar p_l>p_h$, then $V=0$.
--
--   These are the volumes on which the manufacturer's peak-period problem (1) is built.
--
--   **Formalization Note** The page states the interior cases for $\bar p_h\le a$ and $\bar p_l\in[p_h-a,p_h]$. From Table 1 (and the proof, Online Appendix pp. 2–3), the interior formulas hold with $r_h$ in place of $a$, and the upgrade formula also needs $\bar p_h\ge0$. The statement gives the remaining rate cases so that the volumes are characterized for every real rate; it retains the page's correct outer cases $\bar p_h>a$ and $\bar p_l<p_h-a$ as explicit consequences.
-- source:
--   Shi, Hu, Battery as a Service: Flexible Electric Vehicle Battery Leasing, M&SOM (2024), doi:10.1287/msom.2022.0587, authors' manuscript of 13 January 2024, p. 13, Lemma 2; proof Online Appendix pp. 2–3 (PDF 34–35)

import Mathlib
import Definitions.Def_BatteryLease_WinWin_Setting

namespace BatteryLease.WinWin
theorem lemma_2 (a ρ rh ch τ ph pbh pbl : ℝ) (hS : Standing a ρ rh ch)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (pbh < 0 → upVol a rh τ pbh = τ) ∧
    (0 ≤ pbh → pbh ≤ rh → upVol a rh τ pbh = τ * (a - pbh) / a) ∧
    (rh < pbh → upVol a rh τ pbh = 0) ∧
    (a < pbh → upVol a rh τ pbh = 0) ∧
    (pbl < ph - rh → downVol a rh τ ph pbl = 1 - τ) ∧
    (ph - rh ≤ pbl → pbl ≤ ph → downVol a rh τ ph pbl = (1 - τ) * (ph - pbl) / a) ∧
    (pbl < ph - a → downVol a rh τ ph pbl = 1 - τ) ∧
    (ph < pbl → downVol a rh τ ph pbl = 0) := by sorry
end BatteryLease.WinWin
