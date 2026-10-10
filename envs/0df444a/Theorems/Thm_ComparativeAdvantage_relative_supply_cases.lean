-- Prove2me | Theorems.Thm_ComparativeAdvantage_relative_supply_cases
-- name    : ComparativeAdvantage.relative_supply_cases
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:57.643928+00:00
-- url     : https://prove2.me/theorems/f58ad64d-9d51-48c0-b996-42b86dee2f2d
-- title:
--   World relative supply of cloth: the five cases
-- statement:
--   Let Home have a comparative advantage in cloth, $a_{LC}/a_{LW}<a'_{LC}/a'_{LW}$, and let world prices satisfy $P_C,P_W>0$. Write $p=P_C/P_W$. A *competitive output* of a country is a full-employment bundle in which labour works only in sectors paying the highest wage ($P_C/a_{LC}$ in cloth, $P_W/a_{LW}$ in wine). Then:
--
--   1. If $p=a_{LC}/a_{LW}$: every competitive output of Foreign is $(0,L'/a'_{LW})$ (Foreign specializes in wine), and for every $x$ with $0\le x\le L/a_{LC}$ Home has a competitive output producing exactly $x$ units of cloth (Home workers are indifferent, so cloth supply can take any feasible value).
--   2. If $p<a_{LC}/a_{LW}$: for all competitive outputs of Home and Foreign, world cloth output is $0$ (both specialize in wine).
--   3. If $a_{LC}/a_{LW}<p<a'_{LC}/a'_{LW}$: Home's competitive output is $(L/a_{LC},0)$, Foreign's is $(0,L'/a'_{LW})$, and world relative supply is
--   $$\frac{Q_C+Q'_C}{Q_W+Q'_W}=\frac{L/a_{LC}}{L'/a'_{LW}}.$$
--   4. If $p>a'_{LC}/a'_{LW}$: world wine output is $0$ (both specialize in cloth).
--   5. If $p=a'_{LC}/a'_{LW}$: every competitive output of Home is $(L/a_{LC},0)$, and for every $y$ with $0\le y\le L'/a'_{LW}$ Foreign has a competitive output producing exactly $y$ units of wine.
--
--   This is the shape of the step-shaped relative supply curve $RS$.
-- source:
--   Wikipedia, "Comparative advantage" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Comparative_advantage, section "Ricardian model"

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

namespace ComparativeAdvantage

theorem relative_supply_cases (h f : Country) (hCA : HasComparativeAdvantageInCloth h f)
    (PC PW : ℝ) (hPC : 0 < PC) (hPW : 0 < PW) :
    (PC / PW = h.aLC / h.aLW →
      (∀ qF, IsCompetitiveOutput f PC PW qF → qF = (0, f.L / f.aLW)) ∧
      ∀ x ∈ Set.Icc 0 (h.L / h.aLC), ∃ qH, IsCompetitiveOutput h PC PW qH ∧ qH.1 = x) ∧
    (PC / PW < h.aLC / h.aLW →
      ∀ qH qF, IsCompetitiveOutput h PC PW qH → IsCompetitiveOutput f PC PW qF →
        qH.1 + qF.1 = 0) ∧
    (h.aLC / h.aLW < PC / PW → PC / PW < f.aLC / f.aLW →
      ∀ qH qF, IsCompetitiveOutput h PC PW qH → IsCompetitiveOutput f PC PW qF →
        qH = (h.L / h.aLC, 0) ∧ qF = (0, f.L / f.aLW) ∧
        (qH.1 + qF.1) / (qH.2 + qF.2) = (h.L / h.aLC) / (f.L / f.aLW)) ∧
    (f.aLC / f.aLW < PC / PW →
      ∀ qH qF, IsCompetitiveOutput h PC PW qH → IsCompetitiveOutput f PC PW qF →
        qH.2 + qF.2 = 0) ∧
    (PC / PW = f.aLC / f.aLW →
      (∀ qH, IsCompetitiveOutput h PC PW qH → qH = (h.L / h.aLC, 0)) ∧
      ∀ y ∈ Set.Icc 0 (f.L / f.aLW), ∃ qF, IsCompetitiveOutput f PC PW qF ∧ qF.2 = y) := by
  sorry

end ComparativeAdvantage
