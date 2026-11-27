-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_Supplement_theorem_7
-- name    : AssortSearch.MNLQC.Supplement.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:23:39.441994+00:00
-- url     : https://prove2.me/theorems/f2809306-180a-4121-97d7-0993dacab9d8
-- title:
--   Theorem 7 (both search models) — the no-search model under-estimates no-purchase demand at narrower and over-estimates it at deeper assortments
-- statement:
--   Let the variants be labelled by decreasing preference, $v_1\ge v_2\ge\dots\ge v_n>0$, with no-purchase preference $v_0>0$. Consumers follow one of the paper's two search models:
--
--   - the **independent assortment model**, with constant $\lambda=\exp[-(\bar U/\mu+\gamma)]>0$ (Theorem 1), true demands $d_i(x)=q_i^m(x)(1-H(x))$ and $H(x)=\exp(-\lambda(v_0+\sum_{j\le x}v_j))$;
--   - the **overlapping assortment model**, with Gumbel scale $\mu>0$ and search cost $b>0$, true demands $d_i(x)=q_i^m(x)(1-H(\bar U(x),x))$ from Theorem 3 with the depth-dependent threshold $\bar U(x)$, and no search at the full assortment $x=n$.
--
--   In either model $d_0(x)=1-\sum_{i\le x}d_i(x)$. Take any assortment $1\le x\le n$ and the preferences estimated from it, $\hat v(x)=(\hat v_0(x),\dots,\hat v_x(x),\hat v_{x+1}(n),\dots,\hat v_n(n))$, normalised by $\hat v_1=1$. Write $q_0^m(x'\mid\hat v(x))=\hat v_0(x)/(\hat v_0(x)+\sum_{j\le x'}\hat v_j(x))$ for the no-search model's no-purchase share with these estimates. Then, in each of the two models:
--
--   1. with any narrower assortment $x'<x$, the no-search model under-estimates the no-purchase demand,
--   $$d_0(x')\ \ge\ q_0^m(x'\mid\hat v(x));$$
--   2. with any deeper assortment $x<x''\le n$, it over-estimates the no-purchase demand,
--   $$d_0(x'')\ \le\ q_0^m(x''\mid\hat v(x)).$$
--
--   Consumer search is more likely in narrower assortments, but the preference estimates do not reflect it. So a retailer using the no-search model over-estimates its demand at narrower assortments and under-estimates it at deeper ones.
--
--   **Formalization Note** The statement is the conjunction of the two models. The independent conjunct is verbatim the published `AssortSearch.HeurEq.theorem_7` (objects of `AssortSearch.HeurEq.Model`), and the overlapping conjunct uses the objects of `AssortSearch.MNLQC.Supplement.Model`. $x'=0$ is allowed, where $d_0(0)=1$. The labelling $v_1\ge\dots\ge v_n$ (`Antitone v`) is the paper's standing convention of §3. Variants are 0-based.
--
--   Differences from the source:
--   - reading: Theorem 7, stated once, with a proof for the independent model that ends "The similar logic can also be applied to show the results for the overlapping assortment" → the conjunction of the independent-model claim (the published HeurEq.theorem_7 verbatim) and the overlapping-model claim; reason: the theorem is asserted for both search models of the paper; §5.1's d_i(x) is the expected demand of whichever model governs consumers
--   - encoding: λ = exp[−(Ū/μ + γ)] of the independent model → a free parameter λ > 0; reason: every real Ū gives some λ > 0 and every λ > 0 arises from some Ū; same instances
--   - encoding: "take any assortment x", narrower x′ < x, deeper x″ > x → 1 ≤ x ≤ n, 0 ≤ x′ < x, x < x″ ≤ n; reason: depths range over 0, …, n, and v̂(x) is defined only when x ≥ 1 (nothing is observed at x = 0)
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 22 (PDF 24), Theorem 7; proof pp. 22–23 (PDF 24–25)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

namespace AssortSearch.MNLQC.Supplement

/-- **Theorem 7** (p. 22), in both search models. Take any assortment `1 ≤ x ≤ n` and the
preferences `v̂(x)` estimated from it. With any narrower assortment `x' < x` the no-search model
under-estimates the no-purchase demand, `d_0(x') ≥ q_0^m(x' | v̂(x))`; with any deeper assortment
`x < x'' ≤ n` it over-estimates it, `d_0(x'') ≤ q_0^m(x'' | v̂(x))`. The first conjunct is the
independent assortment model (threshold parameter `λ > 0`), the second the overlapping assortment
model (scale `μ > 0`, search cost `b > 0`, threshold `Ū(x)` depending on the depth). -/
theorem theorem_7 {n : ℕ} (lam μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hμ : 0 < μ) (hb : 0 < b)
    (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) :
    ((∀ x' : ℕ, x' < x →
        AssortSearch.HeurEq.shareNoPurchase (AssortSearch.HeurEq.estPref lam v v0 x)
            (AssortSearch.HeurEq.estPrefNoPurchase lam v v0 x) x' ≤
          AssortSearch.HeurEq.demandNoPurchase lam v v0 x') ∧
      (∀ x'' : ℕ, x < x'' → x'' ≤ n →
        AssortSearch.HeurEq.demandNoPurchase lam v v0 x'' ≤
          AssortSearch.HeurEq.shareNoPurchase (AssortSearch.HeurEq.estPref lam v v0 x)
            (AssortSearch.HeurEq.estPrefNoPurchase lam v v0 x) x'')) ∧
    ((∀ x' : ℕ, x' < x →
        AssortSearch.HeurEq.shareNoPurchase (estPrefOv μ b v v0 x)
            (estPrefNoPurchaseOv μ b v v0 x) x' ≤
          demandNoPurchaseOv μ b v v0 x') ∧
      (∀ x'' : ℕ, x < x'' → x'' ≤ n →
        demandNoPurchaseOv μ b v v0 x'' ≤
          AssortSearch.HeurEq.shareNoPurchase (estPrefOv μ b v v0 x)
            (estPrefNoPurchaseOv μ b v v0 x) x'')) := by sorry

end AssortSearch.MNLQC.Supplement
