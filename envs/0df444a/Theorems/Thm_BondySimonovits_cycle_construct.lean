-- Prove2me | Theorems.Thm_BondySimonovits_cycle_construct
-- name    : BondySimonovits.cycle_construct
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:04:05.449801+00:00
-- url     : https://prove2.me/theorems/0866d11d-5faf-4db6-a2d1-5fbfc19355a1
-- title:
--   Bondy Simonovits: cycle construct
-- statement:
--   Closing the cycle: two tree paths from a common ancestor at level `j` to `e` and to the end
--   of a path `q` of length `m = 2k - 2(i - j) - 1` (through layers `≥ i`) starting at a neighbour
--   of `e`, form a cycle of length `2k`.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSCycle.lean#L76-L181
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSCycle.lean#L76-L181

module
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Definitions.Def_BondySimonovitsLib_BSCycle
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V) [DecidableRel K.Adj]
omit [DecidableRel K.Adj]

theorem BondySimonovits.cycle_construct {par : V → V} {x : V}
    (hpar : ∀ v, K.Reachable x v → 0 < K.dist x v →
      K.Adj v (par v) ∧ K.dist x (par v) + 1 = K.dist x v)
    (k i j : ℕ) (hk : 2 ≤ k) (hik : i + 1 ≤ k) (hji' : j < i)
    (e : V) (q : ℕ → V) (m : ℕ) (hmdef : m = 2 * k - 2 * (i - j) - 1)
    (her : K.Reachable x e) (hel : K.dist x e = i) (hzr : K.Reachable x (q m))
    (hzl : K.dist x (q m) = i) (hwe : K.Adj e (q 0))
    (hqadj : ∀ t < m, K.Adj (q t) (q (t + 1))) (hqlev : ∀ t ≤ m, i ≤ K.dist x (q t))
    (hqinj : ∀ s ≤ m, ∀ t ≤ m, q s = q t → s = t) (hqe : ∀ t ≤ m, q t ≠ e)
    (hyz : anc K par x j (q m) = anc K par x j e)
    (hdiff : anc K par x (j + 1) e ≠ anc K par x (j + 1) (q m)) :
    ∃ (v : V) (p : K.Walk v v), p.IsCycle ∧ p.length = 2 * k := by sorry
