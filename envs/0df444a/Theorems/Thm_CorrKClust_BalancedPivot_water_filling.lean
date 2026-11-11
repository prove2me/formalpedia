-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_water_filling
-- name    : CorrKClust.BalancedPivot.water_filling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:03.916364+00:00
-- url     : https://prove2.me/theorems/59f19218-e1b9-4a63-8f60-760099a539d9
-- title:
--   §7.3.4, (13)–(14) — water-filling characterization and threshold test
-- statement:
--   Let w be a multiset of q positive integer sizes, let $q>k\ge1$, and let $a=a(w,k)$ and $r=r(w,k)$ use Definition 3.3's strict stopping test. Put $F(x)=\sum_{w_i\in w}\min\{w_i,x\}$. Then a > 0 and
--   $$F(a)=ka,\qquad r=\#\{i:w_i\ge a\}<k,\qquad\sum_{i:w_i<a}w_i=(k-r)a.$$
--   For every b > 0,
--   $$F(b)>kb\Longrightarrow a>b.$$
--   Equal-size copies are counted with their multiplicities, and sizes exactly a belong among the peeled sizes. This is the deterministic characterization used by the Large-U case.
--
--   Differences from the source:
--   - encoding: final positive pivot-cluster sizes w_1 ≥ ⋯ ≥ w_q with q > k → a positive-integer multiset with k > 0, sorted inside the parameter definitions; reason: the passage uses only these sizes and their multiplicities; every pivot-size family is such a multiset
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), §7.3.4, equations (13)–(14), pp. 39–40, p. 39, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- §7.3.4, (13)--(14), pp. 39--40: the entire deterministic characterization. -/
theorem water_filling (w : Multiset ℕ) (hw : ∀ x ∈ w, 0 < x)
    (k : ℕ) (hk : 0 < k) (hq : k < w.card) :
    let a := cliqueA w k
    let r := cliqueR w k
    0 < a ∧ waterFill w a = (k : ℝ) * a ∧
    r = (w.filter (fun x => a ≤ (x : ℝ))).card ∧ r < k ∧
    ((w.filter (fun x => (x : ℝ) < a)).map (fun x => (x : ℝ))).sum = ((k - r : ℕ) : ℝ) * a ∧
    (∀ b : ℝ, 0 < b → (k : ℝ) * b < waterFill w b → b < a) := by sorry

end CorrKClust.BalancedPivot
