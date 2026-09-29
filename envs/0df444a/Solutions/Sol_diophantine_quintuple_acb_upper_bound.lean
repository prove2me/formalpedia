-- Prove2me | solution 1 for diophantine_quintuple_acb_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T08:13:39.286598+00:00
-- url     : https://prove2.me/submissions/5305b968-32a2-49ba-9290-09dce0258efc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_diophantine_descent
import Theorems.Thm_diophantine_quintuple_b_gt_3a
import Theorems.Thm_diophantine_quintuple_fujita_regular
import Theorems.Thm_diophantine_quadruple_extension_criterion
import Theorems.Thm_diophantine_quintuple_abde_irregular
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic

set_option autoImplicit false

open DiophantineDescent

/-
Exact reduction for the parent target
`Theorems/Thm_diophantine_quintuple_acb_upper_bound.lean`
(`f 0 * f 2 * 20 < 3609 * f 1 ^ 3`, i.e. `ac < 180.45 b^3`).

Source: 1610.04020v2.tex Lemma `lem:acb` and its proof. The deep inputs are
imported as scratch children (compiled to `.olean` under
`work/PiAcbWorkspace/`, checked with that scratch root prepended to the lake
`LEAN_PATH`/`LEAN_SRC_PATH`):
* `diophantine_quintuple_b_gt_3a` — Lemma `lem:b3a` (Cipu–Filipin–Fujita):
  `b > 3a`. Used in the threshold case split below (it rules out the `b<2a`
  case and selects between the `4.321` and `721.8` cases), not for positivity.
* `diophantine_quintuple_fujita_regular` — Theorem `thm:fujita` (Fujita):
  `d = d_+(a,b,c)` with explicit roots. Feeds the elementary lower bound.
* `diophantine_quadruple_extension_criterion` — Lemma `lem:cb`
  (Fujita–Miyazaki): each `b/a` case has its OWN threshold (`9.864 b^4` if
  `b < 2a`, `4.321 b^4` if `2a ≤ b ≤ 12a`, `721.8 b^4` if `b > 12a`); reaching
  it forces `d = d_+`. Applied contrapositively to `{a,b,d,e}`.
* `diophantine_quintuple_abde_irregular` — the irregularity asserted in the
  `lem:acb` proof ("Consider the irregular Diophantine quadruple
  `{a, b, d, e}`", no lemma number given). Honestly isolated: it is the
  hypothesis that lets the criterion yield strict upper bounds.
Everything else (root comparison, case collapses, final cancellation) is
proved here from those children. This file contains no unfinished proofs
and declares no axioms.
-/

/-- Algebra core of `lem:acb`: `4abc < d` and `5d < 3609 b^4` give
`20ac < 3609 b^3` for `0 < b`. Constants: `721.8 = 3609/5` and
`721.8/4 = 180.45 = 3609/20`. -/
theorem pi_acb_exact_algebra (a b c d : Nat)
    (hLow : 4 * a * b * c < d) (hHigh : 5 * d < 3609 * b ^ 4)
    (hb : 0 < b) : a * c * 20 < 3609 * b ^ 3 := by
  have h5 : 5 * (4 * a * b * c) < 5 * d :=
    Nat.mul_lt_mul_of_pos_left hLow (by norm_num)
  have hChain : 5 * (4 * a * b * c) < 3609 * b ^ 4 := lt_trans h5 hHigh
  have h20 : 20 * a * b * c < 3609 * b ^ 4 := by
    have e : 20 * a * b * c = 5 * (4 * a * b * c) := by ring
    rw [e]
    exact hChain
  have eL : 20 * a * b * c = (a * c * 20) * b := by ring
  have eR : 3609 * b ^ 4 = (3609 * b ^ 3) * b := by ring
  rw [eL, eR] at h20
  exact (Nat.mul_lt_mul_right hb).mp h20

/-- Elementary half of `lem:d+ieq` (Dujella, p.189): an explicitly regular
extension `d = a+b+c+2abc+2rst` exceeds `4abc`, since
`(rst)^2 = (ab+1)(ac+1)(bc+1) > (ab)(ac)(bc) = (abc)^2`. -/
theorem pi_acb_exact_dplus_lower (a b c d r s t : Nat)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : a * b + 1 = r ^ 2) (hs : a * c + 1 = s ^ 2)
    (ht : b * c + 1 = t ^ 2)
    (hd : d = a + b + c + 2 * a * b * c + 2 * r * s * t) :
    4 * a * b * c < d := by
  have eABC : (a * b * c) ^ 2 = (a * b) * (a * c) * (b * c) := by ring
  have eRST : (r * s * t) ^ 2 = (r ^ 2) * (s ^ 2) * (t ^ 2) := by ring
  have eProd : (a * b + 1) * (a * c + 1) * (b * c + 1)
      = (a * b) * (a * c) * (b * c)
        + ((a * b) * (a * c) + (a * b) * (b * c) + (a * c) * (b * c)
          + (a * b) + (a * c) + (b * c) + 1) := by ring
  have hlt : (a * b) * (a * c) * (b * c)
      < (a * b + 1) * (a * c + 1) * (b * c + 1) := by omega
  have hsq : (a * b * c) ^ 2 < (r * s * t) ^ 2 := by
    rw [eABC, eRST, ← hr, ← hs, ← ht]
    exact hlt
  have hrst : a * b * c < r * s * t := by
    by_contra hcon
    have hle : r * s * t ≤ a * b * c := le_of_not_gt hcon
    have hle2 : (r * s * t) ^ 2 ≤ (a * b * c) ^ 2 :=
      Nat.pow_le_pow_left hle 2
    omega
  have e1 : 2 * a * b * c = 2 * (a * b * c) := by ring
  have e2 : 2 * r * s * t = 2 * (r * s * t) := by ring
  have e3 : 4 * a * b * c = 4 * (a * b * c) := by ring
  rw [e1, e2] at hd
  rw [e3]
  omega

/-- The `2a ≤ b ≤ 12a` case of `lem:cb` implies the bound used in `lem:acb`:
`d < 4.321 b^4` (i.e. `1000d < 4321b^4`) gives `d < 721.8 b^4`
(i.e. `5d < 3609b^4`), since `4.321 < 721.8`. -/
theorem pi_acb_exact_case_mid (b d : Nat)
    (h : 1000 * d < 4321 * b ^ 4) : 5 * d < 3609 * b ^ 4 := by
  omega

/-- The `b > 12a` case of `lem:cb`, restated: `d < 721.8 b^4`
(i.e. `1000d < 721800b^4`) is `5d < 3609b^4` (divide by 200). -/
theorem pi_acb_exact_case_top (b d : Nat)
    (h : 1000 * d < 721800 * b ^ 4) : 5 * d < 3609 * b ^ 4 := by
  omega

/-- Exact parent statement: every ordered Diophantine quintuple satisfies
`20ac < 3609b^3`. -/
theorem solution (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) : f 0 * f 2 * 20 < 3609 * f 1 ^ 3 := by
  have hpos : ∀ i, 0 < f i := hq.1
  have hsq : ∀ i j, i ≠ j → ∃ r : Nat, f i * f j + 1 = r ^ 2 := hq.2.2
  have h01 : f 0 < f 1 := ho.1
  have h12 : f 1 < f 2 := ho.2.1
  have h23 : f 2 < f 3 := ho.2.2.1
  have h34 : f 3 < f 4 := ho.2.2.2
  -- Lemma `lem:b3a`: `b > 3a`. Used below to kill the `b < 2a` case of the
  -- criterion and to choose between the `4.321` and `721.8` cases.
  have hB : 3 * f 0 < f 1 := diophantine_quintuple_b_gt_3a f hq ho
  -- Theorem `thm:fujita`: `{a,b,c,d}` is regular; the elementary lower half
  -- of `lem:d+ieq` then gives `4abc < d`.
  obtain ⟨r0, s0, t0, hr0, hs0, ht0, hreg⟩ :=
    diophantine_quintuple_fujita_regular f hq ho
  have hLow : 4 * f 0 * f 1 * f 2 < f 3 :=
    pi_acb_exact_dplus_lower _ _ _ _ _ _ _ (hpos 0) (hpos 1) (hpos 2)
      hr0 hs0 ht0 hreg
  -- The quadruple `{a,b,d,e}` is Diophantine with `a < b < d < e`.
  have h13 : f 1 < f 3 := lt_trans h12 h23
  obtain ⟨r1, hr1⟩ := hsq 0 1 (by decide)
  obtain ⟨s1, hs1⟩ := hsq 0 3 (by decide)
  obtain ⟨t1, ht1⟩ := hsq 1 3 (by decide)
  obtain ⟨u1, hu1⟩ := hsq 0 4 (by decide)
  obtain ⟨v1, hv1⟩ := hsq 1 4 (by decide)
  obtain ⟨w1, hw1⟩ := hsq 3 4 (by decide)
  -- It is irregular (explicit child): `e ≠ d_+(a,b,d)`.
  have hirr : f 4 ≠ f 0 + f 1 + f 3 + 2 * f 0 * f 1 * f 3 + 2 * r1 * s1 * t1 :=
    diophantine_quintuple_abde_irregular f hq ho r1 s1 t1 hr1 hs1 ht1
  -- Since `3a < b`, certainly `2a < b`: the `b < 2a` case is dead.
  have h2a : 2 * f 0 < f 1 := by omega
  -- Contrapositive of `lem:cb` on `{a,b,d,e}`: each live `b/a` case yields
  -- its own strict upper bound on `d`, both implying `5d < 3609b^4`.
  have hsplit : f 1 ≤ 12 * f 0 ∨ 12 * f 0 < f 1 := by omega
  have hHigh : 5 * f 3 < 3609 * f 1 ^ 4 := by
    rcases hsplit with hle | hgt
    · have h2ale : 2 * f 0 ≤ f 1 := by omega
      have hlt : 1000 * f 3 < 4321 * f 1 ^ 4 := by
        by_contra hcon
        have hge : 4321 * f 1 ^ 4 ≤ 1000 * f 3 := le_of_not_gt hcon
        have heq := diophantine_quadruple_extension_criterion
          (f 0) (f 1) (f 3) (f 4) (hpos 0) h01 h13 h34
          ⟨r1, hr1⟩ ⟨s1, hs1⟩ ⟨t1, ht1⟩ ⟨u1, hu1⟩ ⟨v1, hv1⟩ ⟨w1, hw1⟩
          r1 s1 t1 hr1 hs1 ht1
          (Or.inr (Or.inl ⟨h2ale, hle, hge⟩))
        exact hirr heq
      exact pi_acb_exact_case_mid _ _ hlt
    · have hlt : 1000 * f 3 < 721800 * f 1 ^ 4 := by
        by_contra hcon
        have hge : 721800 * f 1 ^ 4 ≤ 1000 * f 3 := le_of_not_gt hcon
        have heq := diophantine_quadruple_extension_criterion
          (f 0) (f 1) (f 3) (f 4) (hpos 0) h01 h13 h34
          ⟨r1, hr1⟩ ⟨s1, hs1⟩ ⟨t1, ht1⟩ ⟨u1, hu1⟩ ⟨v1, hv1⟩ ⟨w1, hw1⟩
          r1 s1 t1 hr1 hs1 ht1
          (Or.inr (Or.inr ⟨hgt, hge⟩))
        exact hirr heq
      exact pi_acb_exact_case_top _ _ hlt
  exact pi_acb_exact_algebra _ _ _ _ hLow hHigh (hpos 1)

#print axioms solution
