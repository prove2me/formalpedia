-- Prove2me | solution 1 for diophantine_quintuple_abde_irregular
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T10:12:58.179879+00:00
-- url     : https://prove2.me/submissions/fbf6e5de-bd23-4798-91cb-01cf0ff73860
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Direct proof of `diophantine_quintuple_abde_irregular`
(`e ≠ d₊(a,b,d)` in an ordered Diophantine quintuple).

Mathematical argument (all identities over ℤ, verified by `linear_combination`
with the recorded certificates, hence by `ring`):

Let a=f 0, b=f 1, c=f 2, d=f 3, e=f 4, with r²=ab+1, s²=ad+1, t²=bd+1.
Fujita regularity (imported child) gives p,q with p²=ac+1, q²=bc+1 and
  d = a+b+c+2abc+2rpq.                                          (F)

(1) Explicit roots above d: (aq+rp)²=ad+1 and (bp+rq)²=bd+1. Indeed, with (F),
  (aq+rp)²-(ad+1) = p²(r²-ab-1)+(ab+1)(p²-ac-1)+a²(q²-bc-1),
and symmetrically for t. Since squares determine the root in ℕ,
  s = aq+rp,  t = bp+rq.                                        (R)

(2) Key identity. With M := d-a-b and (F),(R) substituted, E := M²-c·e-4ab-4
satisfies
  E = (2ac+2bc-2cpqr+4)(r²-ab-1) + (2q²r²+2r²)(p²-ac-1)
      + (2p²r²+2r²)(q²-bc-1),
so E = 0, i.e.
  (d-a-b)² = c·e + 4ab + 4 = c·e + (2r)².                       (K)
(In particular, with N := c·e+1 = w² from the quintuple hypothesis,
N = M²-(4ab+3) where M = d-a-b.)

(3) Between-squares trap. M = c+2abc+2rpq ≥ 1+2ab+2·1 = 2ab+3 > 2ab+2
(using c,r,p,q ≥ 1), so with D := 4ab+3 > 0 one has 0 < D < 2M-1, i.e.
  (M-1)² = M²-2M+1 < M²-D = N < M².
Concretely hdiff_up/hdiff_low isolate the linear content for `omega`, and
monotonicity of squares (`pow_le_pow_left₀`) forces M-1 < w < M over ℤ,
impossible. Hence the assumed regular value for e is contradictory.

The load-bearing witness is c·e+1 (the only square condition not forced by
the two regular extensions); numerically e.g. (1,3,8)→d=120→e=1680 gives
8·1680+1=13441=116²-15 with 116=d-a-b, never a square.
-/
import Definitions.Def_diophantine_descent
import Theorems.Thm_diophantine_quintuple_fujita_regular
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
open DiophantineDescent

theorem nat_eq_of_sq_eq {m n : Nat} (h : m ^ 2 = n ^ 2) : m = n := by
  rcases lt_trichotomy m n with h1 | h1 | h1
  · have h2 : m ^ 2 < n ^ 2 := pow_lt_pow_left₀ h1 (Nat.zero_le _) (by norm_num)
    exact absurd h (ne_of_lt h2)
  · exact h1
  · have h2 : n ^ 2 < m ^ 2 := pow_lt_pow_left₀ h1 (Nat.zero_le _) (by norm_num)
    exact absurd h.symm (ne_of_lt h2)

theorem int_eq_of_sq_eq {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 = y ^ 2) : x = y := by
  rcases lt_trichotomy x y with h1 | h1 | h1
  · have h2 : x ^ 2 < y ^ 2 := pow_lt_pow_left₀ h1 hx (by norm_num)
    exact absurd h (ne_of_lt h2)
  · exact h1
  · have h2 : y ^ 2 < x ^ 2 := pow_lt_pow_left₀ h1 hy (by norm_num)
    exact absurd h.symm (ne_of_lt h2)

theorem solution (f : Fin 5 → Nat)
    (hq : Quintuple f)
    (ho : Ordered f) (r s t : Nat)
    (hr : f 0 * f 1 + 1 = r ^ 2)
    (hs : f 0 * f 3 + 1 = s ^ 2)
    (ht : f 1 * f 3 + 1 = t ^ 2) :
    f 4 ≠ f 0 + f 1 + f 3 + 2 * f 0 * f 1 * f 3 + 2 * r * s * t := by
  intro heq
  obtain ⟨r0, p, q, hr0, hp, hqq, hdfuj⟩ :=
    diophantine_quintuple_fujita_regular f hq ho
  obtain ⟨w, hw⟩ := hq.2.2 2 4 (by decide)
  set a := f 0 with ha_def
  set b := f 1 with hb_def
  set c := f 2 with hc_def
  set d := f 3 with hd_def
  set e := f 4 with he_def
  have hpos : ∀ i, 0 < f i := hq.1
  have ha_pos : 0 < a := hpos 0
  have hb_pos : 0 < b := hpos 1
  have hc_pos : 0 < c := hpos 2
  have hd_pos : 0 < d := hpos 3
  have he_pos : 0 < e := hpos 4
  have h01 : a < b := ho.1
  have h12 : b < c := ho.2.1
  have h23 : c < d := ho.2.2.1
  have h34 : d < e := ho.2.2.2
  have hrr_eq : r0 ^ 2 = r ^ 2 := by rw [← hr0, ← hr]
  have hr0r : r0 = r := nat_eq_of_sq_eq hrr_eq
  rw [hr0r] at hdfuj
  have hr_ne : r ≠ 0 := by
    intro hz
    subst hz
    simp at hr
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr_ne
  have hp_ne : p ≠ 0 := by
    intro hz
    subst hz
    simp at hp
  have hp1 : 1 ≤ p := Nat.pos_of_ne_zero hp_ne
  have hq_ne : q ≠ 0 := by
    intro hz
    subst hz
    simp at hqq
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero hq_ne
  have hrrI : (r : Int) ^ 2 = (a : Int) * (b : Int) + 1 := by
    exact_mod_cast hr.symm
  have hppI : (p : Int) ^ 2 = (a : Int) * (c : Int) + 1 := by
    exact_mod_cast hp.symm
  have hqqI : (q : Int) ^ 2 = (b : Int) * (c : Int) + 1 := by
    exact_mod_cast hqq.symm
  have hdI : (d : Int) = (a : Int) + (b : Int) + (c : Int)
      + 2 * (a : Int) * (b : Int) * (c : Int)
      + 2 * (r : Int) * (p : Int) * (q : Int) := by
    exact_mod_cast hdfuj
  have hsI : (s : Int) ^ 2 = (a : Int) * (d : Int) + 1 := by
    exact_mod_cast hs.symm
  have htI : (t : Int) ^ 2 = (b : Int) * (d : Int) + 1 := by
    exact_mod_cast ht.symm
  have heqI : (e : Int) = (a : Int) + (b : Int) + (d : Int)
      + 2 * (a : Int) * (b : Int) * (d : Int)
      + 2 * (r : Int) * (s : Int) * (t : Int) := by
    exact_mod_cast heq
  have hspI : ((a : Int) * (q : Int) + (r : Int) * (p : Int)) ^ 2
      = (a : Int) * (d : Int) + 1 := by
    linear_combination (p : Int) ^ 2 * hrrI
      + ((a : Int) * (b : Int) + 1) * hppI + (a : Int) ^ 2 * hqqI - (a : Int) * hdI
  have htpI : ((b : Int) * (p : Int) + (r : Int) * (q : Int)) ^ 2
      = (b : Int) * (d : Int) + 1 := by
    linear_combination (q : Int) ^ 2 * hrrI
      + ((a : Int) * (b : Int) + 1) * hqqI + (b : Int) ^ 2 * hppI - (b : Int) * hdI
  have hsE : (s : Int) = (a : Int) * (q : Int) + (r : Int) * (p : Int) := by
    apply int_eq_of_sq_eq (Nat.cast_nonneg _) (by positivity)
    rw [hsI, hspI]
  have htE : (t : Int) = (b : Int) * (p : Int) + (r : Int) * (q : Int) := by
    apply int_eq_of_sq_eq (Nat.cast_nonneg _) (by positivity)
    rw [htI, htpI]
  have keyI : ((d : Int) - (a : Int) - (b : Int)) ^ 2
      = (c : Int) * (e : Int) + 4 * (a : Int) * (b : Int) + 4 := by
    rw [heqI, hsE, htE, hdI]
    linear_combination (2 * (a : Int) * (c : Int) + 2 * (b : Int) * (c : Int)
      - 2 * (c : Int) * (p : Int) * (q : Int) * (r : Int) + 4) * hrrI
      + (2 * (q : Int) ^ 2 * (r : Int) ^ 2 + 2 * (r : Int) ^ 2) * hppI
      + (2 * (p : Int) ^ 2 * (r : Int) ^ 2 + 2 * (r : Int) ^ 2) * hqqI
  have hwI : (w : Int) ^ 2 = (c : Int) * (e : Int) + 1 := by
    exact_mod_cast hw.symm
  set MI : Int := (d : Int) - (a : Int) - (b : Int) with hMI_def
  have hMI_nn : 0 ≤ MI := by
    have hle : a + b ≤ d := by omega
    have hleI : (a : Int) + (b : Int) ≤ (d : Int) := by exact_mod_cast hle
    omega
  have hMlo : 2 * (a : Int) * (b : Int) + 2 < MI := by
    have hc1 : 1 ≤ c := hc_pos
    have h1 : 2 * a * b ≤ 2 * a * b * c := by
      calc 2 * a * b = 2 * a * b * 1 := by ring
        _ ≤ 2 * a * b * c := Nat.mul_le_mul_left _ hc1
    have hrpq : 1 ≤ r * p * q := Nat.one_le_iff_ne_zero.mpr (by
      apply mul_ne_zero
      · apply mul_ne_zero
        · exact hr_ne
        · exact hp_ne
      · exact hq_ne)
    have h2 : 2 ≤ 2 * r * p * q := by
      calc (2 : Nat) = 2 * 1 := by ring
        _ ≤ 2 * (r * p * q) := Nat.mul_le_mul_left 2 hrpq
        _ = 2 * r * p * q := by ring
    have hMnat : 2 * a * b + 3 ≤ c + 2 * a * b * c + 2 * r * p * q := by omega
    have hdM : d = a + b + (c + 2 * a * b * c + 2 * r * p * q) := by omega
    have hdMI : MI = (c : Int) + 2 * (a : Int) * (b : Int) * (c : Int)
        + 2 * (r : Int) * (p : Int) * (q : Int) := by
      rw [hMI_def, hdM]
      push_cast
      ring
    have hMnatI : 2 * (a : Int) * (b : Int) + 3
        ≤ (c : Int) + 2 * (a : Int) * (b : Int) * (c : Int)
          + 2 * (r : Int) * (p : Int) * (q : Int) := by
      exact_mod_cast hMnat
    omega
  have hab_nn : (0 : Int) ≤ (a : Int) * (b : Int) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hdiff_up : MI ^ 2 - (w : Int) ^ 2 = 4 * (a : Int) * (b : Int) + 3 := by
    linear_combination keyI - hwI
  have hpos_up : (0 : Int) < 4 * (a : Int) * (b : Int) + 3 := by positivity
  have hup : (w : Int) ^ 2 < MI ^ 2 := by omega
  have hdiff_low : (w : Int) ^ 2 - (MI - 1) ^ 2
      = 2 * (MI - (2 * (a : Int) * (b : Int) + 2)) := by
    linear_combination hwI - keyI
  have hlow : (MI - 1) ^ 2 < (w : Int) ^ 2 := by omega
  have hw_lt : (w : Int) < MI := by
    by_contra hcon
    have hle : MI ≤ (w : Int) := by omega
    have hsq : MI ^ 2 ≤ (w : Int) ^ 2 :=
      pow_le_pow_left₀ hMI_nn hle 2
    have hcontra : MI ^ 2 < MI ^ 2 := lt_of_le_of_lt hsq hup
    exact (lt_irrefl _) hcontra
  have hMI1_lt : MI - 1 < (w : Int) := by
    by_contra hcon
    have hle : (w : Int) ≤ MI - 1 := by omega
    have hsq : (w : Int) ^ 2 ≤ (MI - 1) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hle 2
    have hcontra : (w : Int) ^ 2 < (w : Int) ^ 2 := lt_of_le_of_lt hsq hlow
    exact (lt_irrefl _) hcontra
  omega
