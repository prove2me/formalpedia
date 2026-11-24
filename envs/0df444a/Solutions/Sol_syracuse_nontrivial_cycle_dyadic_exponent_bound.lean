-- Prove2me | solution 1 for syracuse_nontrivial_cycle_dyadic_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T10:10:51.167796+00:00
-- url     : https://prove2.me/submissions/2070c8ad-2ba8-4d83-afcd-e2dd03bab644

import Theorems.Thm_syracuse_no_cycle_below_two_pow_twenty_three
import Theorems.Thm_syracuse_periodic_reaches_one
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

private abbrev B : ℕ := 8388608
private abbrev D : ℕ := 1048576
private abbrev R : ℕ := 8796093022208

-- A state consists of a mantissa and its accumulated binary exponent.
private def advanceWith (d r : ℕ) (z : ℕ × ℕ) : ℕ × ℕ :=
  let n := 3*z.1+d
  if n+1 ≥ 4*r then ((n+3)/4, z.2+2) else ((n+1)/2, z.2+1)

private def advance (z : ℕ × ℕ) := advanceWith D R z

private theorem rangeWith (d r : ℕ) (hdr : d ≤ r) (z : ℕ × ℕ) (h : z.1 < 2*r) :
    (advanceWith d r z).1 < 2*r := by
  by_cases e : 3*z.1+d+1 ≥ 4*r
  · simpa only [advanceWith, if_pos e] using
      (show (3*z.1+d+3)/4 < 2*r by omega)
  · simpa only [advanceWith, if_neg e] using
      (show (3*z.1+d+1)/2 < 2*r by omega)

private theorem advance_range (z : ℕ × ℕ) (h : z.1 < 2*R) :
    (advance z).1 < 2*R := rangeWith D R (by decide) z h

private theorem boundWith (d r : ℕ) (z : ℕ × ℕ) :
    2^z.2 * (3*z.1+d) ≤ 2^(advanceWith d r z).2 * (advanceWith d r z).1 := by
  by_cases e : 3*z.1+d+1 ≥ 4*r
  · simp only [advanceWith, if_pos e, pow_add, Nat.mul_assoc, Nat.reducePow]
    exact Nat.mul_le_mul_left _ (by omega)
  · simp only [advanceWith, if_neg e, pow_add, Nat.mul_assoc, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)

private theorem advance_bound (z : ℕ × ℕ) :
    2^z.2 * (3*z.1+D) ≤ 2^(advance z).2 * (advance z).1 := boundWith D R z

attribute [irreducible] advance

private def block : ℕ → (ℕ × ℕ) → (ℕ × ℕ)
  | 0, z => advance z
  | h+1, z => block h (block h z)

private theorem block_eq (h : ℕ) (z : ℕ × ℕ) :
    block h z = advance^[2^h] z := by
  induction h generalizing z with
  | zero => simp only [block, pow_zero, Function.iterate_one]
  | succ h ih =>
    rw [block, ih, ih, ← Function.iterate_add_apply, pow_succ, Nat.mul_two]

-- Each block uses a balanced recursion, keeping the certificate stack small.
private def blocks : List ℕ → (ℕ × ℕ) → (ℕ × ℕ)
  | [], z => z
  | h::hs, z => blocks hs (block h z)

private theorem blocks_eq (hs : List ℕ) (z : ℕ × ℕ) :
    blocks hs z = advance^[(hs.map (fun h => 2^h)).sum] z := by
  induction hs generalizing z with
  | nil => rfl
  | cons h hs ih =>
    rw [blocks, ih, block_eq, ← Function.iterate_add_apply, List.map_cons, List.sum_cons, Nat.add_comm]

private theorem extendBlock {n : ℕ} {a b c : ℕ × ℕ}
    (hb : block 12 a = b) (hr : advance^[n] b = c) :
    advance^[4096+n] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply]
  have h : advance^[4096] a = b := (block_eq 12 a).symm.trans hb
  exact (congrArg (advance^[n]) h).trans hr

-- Kernel-check the 4096-step blocks independently.
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem certificate : advance^[143628] (R,0) = (17592101580248,227644) := by
  refine extendBlock (n := 139532) (b := (8836256331731,6492)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 135436) (b := (8876602513169,12984)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 131340) (b := (8917132751903,19476)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 127244) (b := (8957848597876,25968)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 123148) (b := (8998749831085,32460)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 119052) (b := (9039838012346,38952)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 114956) (b := (9081113996129,45444)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 110860) (b := (9122577917062,51936)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 106764) (b := (9164231721492,58428)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 102668) (b := (9206075549013,64920)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 98572) (b := (9248110082443,71412)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 94476) (b := (9290337112642,77904)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 90380) (b := (9332756595839,84396)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 86284) (b := (9375369780523,90888)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 82188) (b := (9418177925334,97380)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 78092) (b := (9461180983637,103872)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 73996) (b := (9504380785274,110364)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 69900) (b := (9547777852579,116856)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 65804) (b := (9591372514332,123348)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 61708) (b := (9635166816835,129840)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 57612) (b := (9679160907694,136332)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 53516) (b := (9723355697187,142824)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 49420) (b := (9767752488684,149316)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 45324) (b := (9812351816489,155808)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 41228) (b := (9857154995055,162300)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 37132) (b := (9902162760673,168792)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 33036) (b := (9947375651786,175284)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 28940) (b := (9992795594463,181776)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 24844) (b := (10038422542909,188268)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 20748) (b := (10084257838930,194760)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 16652) (b := (10130302635412,201252)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 12556) (b := (10176557284918,207744)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 8460) (b := (10223023553849,214236)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 4364) (b := (10269701800329,220728)) (by as_aux_lemma => decide +kernel) ?_
  refine extendBlock (n := 268) (b := (10316592786251,227220)) (by as_aux_lemma => decide +kernel) ?_
  have last : blocks [8,3,2] (10316592786251,227220) = (17592101580248,227644) := by
    change blocks [8,3,2] (10316592786251,227220) = _
    decide +kernel
  exact (blocks_eq [8,3,2] _).symm.trans last

private theorem state_range (j : ℕ) : (advance^[j] (R,0)).1 < 2*R := by
  induction j with
  | zero => decide
  | succ j ih => rw [Function.iterate_succ_apply']; exact advance_range _ ih

private def weight (m n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (3*syracuseStep^[i] m+1).factorization 2

private theorem compare (m n A u : ℕ)
    (hbase : ∀ j : ℕ, B ≤ syracuseStep^[j] m)
    (hstart : 2^A*(D*m) ≤ 2^u*R) :
    2^(A+weight m n)*(D*syracuseStep^[n] m) ≤
      2^(u+(advance^[n] (R,0)).2)*(advance^[n] (R,0)).1 := by
  induction n with
  | zero => simpa [weight] using hstart
  | succ n ih =>
    let x := syracuseStep^[n] m
    let e := (3*x+1).factorization 2
    let z := advance^[n] (R,0)
    let s := A+weight m n
    let t := u+z.2
    change 2^s*(D*x) ≤ 2^t*z.1 at ih
    have hz : z.1 < 2*R := state_range n
    have hx : R ≤ D*x := Nat.mul_le_mul_left D (hbase n)
    have hst : s ≤ t := by
      by_contra! h
      have h2 : (2:ℕ)^(t+1) ≤ 2^s := Nat.pow_le_pow_right (by decide) h
      have low := Nat.mul_le_mul h2 hx
      have high := Nat.mul_lt_mul_of_pos_left hz (Nat.pow_pos (n := t) (by decide : 0 < 2))
      rw [pow_succ, Nat.mul_assoc] at low
      omega
    have hD := Nat.mul_le_mul_right D (Nat.pow_le_pow_right (by decide : 0 < 2) hst)
    have hnext : 2^s*(D*(3*x+1)) ≤ 2^t*(3*z.1+D) := by
      calc
        2^s*(D*(3*x+1)) = 3*(2^s*(D*x)) + 2^s*D := by ring
        _ ≤ 3*(2^t*z.1) + 2^t*D := Nat.add_le_add (Nat.mul_le_mul_left 3 ih) hD
        _ = _ := by ring
    have hstep : 2^e*syracuseStep x = 3*x+1 := Nat.ordProj_mul_ordCompl_eq_self _ 2
    have w : A+weight m (n+1) = s+e := by simp [weight, s, e, x, Finset.sum_range_succ, Nat.add_assoc]
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', w]
    change 2^(s+e)*(D*syracuseStep x) ≤ 2^(u+(advance z).2)*(advance z).1
    calc
      2^(s+e)*(D*syracuseStep x) = 2^s*(D*(2^e*syracuseStep x)) := by rw [pow_add]; ring
      _ ≤ 2^t*(3*z.1+D) := by rw [hstep]; exact hnext
      _ = 2^u*(2^z.2*(3*z.1+D)) := by simp [t, pow_add, Nat.mul_assoc]
      _ ≤ 2^u*(2^(advance z).2*(advance z).1) := Nat.mul_le_mul_left _ (advance_bound z)
      _ = _ := by rw [pow_add, Nat.mul_assoc]

private theorem weight_add (m a b : ℕ) :
    weight m (a+b) = weight m a + weight (syracuseStep^[a] m) b := by
  simp only [weight, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm a i, Function.iterate_add_apply]

private theorem weight_period (m p : ℕ) (h : syracuseStep^[p] m = m) (j : ℕ) :
    weight m (p*j) = j*weight m p ∧ syracuseStep^[p*j] m = m := by
  induction j with
  | zero => simp [weight]
  | succ j ih =>
    rw [Nat.mul_succ, weight_add, ih.2, ih.1, Nat.succ_mul]
    refine ⟨rfl, ?_⟩
    rw [Nat.add_comm, Function.iterate_add_apply, ih.2, h]

private theorem cover (a b : ℕ) (ha : b ≤ a) (hb : 0 < b) :
    ∃ u : ℕ, a ≤ 2^u*b ∧ 2^u*b < 2*a := by
  have hex : ∃ u : ℕ, a ≤ 2^u*b := by
    exact ⟨a,(Nat.le_of_lt (Nat.lt_two_pow_self (n := a))).trans
      (Nat.le_mul_of_pos_right _ hb)⟩
  let u := Nat.find hex
  have hu : a ≤ 2^u*b := Nat.find_spec hex
  refine ⟨u,hu,?_⟩
  cases he : u with
  | zero => simp; omega
  | succ j =>
    have hj : ¬ a ≤ 2^j*b := Nat.find_min hex (show j < u by omega)
    rw [pow_succ, Nat.mul_right_comm (2^j) 2 b]
    omega

theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    143628 * (∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2) ≤
      227645 * p := by
  have base (i : ℕ) : B ≤ syracuseStep^[i] m := by
    apply Nat.le_of_not_gt
    intro hs
    have pos : 0 < syracuseStep^[i] m := by
      cases i with
      | zero => exact hm
      | succ j => rw [Function.iterate_succ_apply']; exact Nat.ordCompl_pos 2 (by omega)
    have ret : syracuseStep^[p] (syracuseStep^[i] m) = syracuseStep^[i] m := by
      rw [← Function.iterate_add_apply, Nat.add_comm p i, Function.iterate_add_apply, hcycle]
    exact hne (syracuse_periodic_reaches_one m p hp hcycle
      ⟨i, syracuse_no_cycle_below_two_pow_twenty_three _ p pos hp hs ret⟩)
  obtain ⟨u,hu,htight⟩ := cover (D*m) R (Nat.mul_le_mul_left D (base 0)) (by decide)
  have many (j : ℕ) :
      2^(weight m (143628*j))*(D*syracuseStep^[143628*j] m) ≤ 2^(u+227645*j)*R := by
    induction j with
    | zero => simpa [weight] using hu
    | succ j ih =>
      let a := 143628*j
      have bx (i : ℕ) : B ≤ syracuseStep^[i] (syracuseStep^[a] m) := by
        rw [← Function.iterate_add_apply]; exact base _
      have run := compare (syracuseStep^[a] m) 143628 (weight m a) (u+227645*j) bx ih
      rw [certificate] at run
      change 2^(weight m a + weight (syracuseStep^[a] m) 143628) *
        (D * syracuseStep^[143628] (syracuseStep^[a] m)) ≤
        2^(u+227645*j+227644)*17592101580248 at run
      rw [← weight_add, ← Function.iterate_add_apply, Nat.add_comm 143628 a] at run
      change 2^(weight m (143628*(j+1)))*(D*syracuseStep^[143628*(j+1)] m) ≤ _
      rw [Nat.mul_succ 143628]
      apply run.trans
      let t := u+227645*j+227644
      calc
        2^t*17592101580248 ≤ 2^t*(2*R) :=
          Nat.mul_le_mul_left _ (by decide : 17592101580248 ≤ 2*R)
        _ = 2^(t+1)*R := by rw [pow_succ 2 t, Nat.mul_assoc]
        _ = 2^(u+227645*(j+1))*R := by
          rw [show t+1 = u+227645*(j+1) by dsimp only [t]; omega]
  have h := many p
  rw [Nat.mul_comm 143628 p, (weight_period m p hcycle 143628).1,
    (weight_period m p hcycle 143628).2] at h
  change 143628*weight m p ≤ 227645*p
  by_contra! bad
  have h2 : (2:ℕ)^(227645*p+1) ≤ 2^(143628*weight m p) :=
    Nat.pow_le_pow_right (by decide) bad
  have hlow := (Nat.mul_le_mul_right (D*m) h2).trans h
  rw [pow_succ, Nat.mul_assoc, Nat.add_comm u, pow_add, Nat.mul_assoc] at hlow
  exact Nat.not_le_of_gt (Nat.mul_lt_mul_of_pos_left htight (Nat.pow_pos (by decide : 0<2))) hlow
