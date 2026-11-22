-- Prove2me | solution 48 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:07.746904+00:00
-- url     : https://prove2.me/submissions/59cc150b-e1ff-48af-b47b-d0d6ffda93a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_NymanBeurling_polynomial_cutoff_rational_gram_criterion
import Theorems.Thm_NymanBeurling_cofinal_subcubic_rational_gram_rows
import Theorems.Thm_NymanBeurling_localized_zero_obstruction
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

-- Step 1: `NymanBeurling.cofinal_subcubic_rational_gram_rows` implies `NymanBeurling.subpower_remainder_certificates` (accepted reduction of `NymanBeurling.subpower_remainder_certificates`).
section

open Finset NymanBeurling.RationalGram
namespace SubcubicCertificate

private theorem budget {n J : ℕ} (hn : 2 ≤ n)
    (hg : gap (n^(J+2)) (512*n^(3*(J+1))) ≤ 1/(J+1:ℚ)) :
    ∃ c : ℕ →₀ ℚ, headEnergy c (512*n^(3*(J+1))) ≤ 1/(J+1:ℚ) ∧
      (cost c (512*n^(3*(J+1))))^(J+1) ≤ ((512*n^(3*(J+1)):ℕ)+1:ℚ) := by
  let D := n^(J+2)
  let H := 512*n^(3*(J+1))
  have dn : n ≤ D := Nat.le_self_pow (by omega) _
  have dH : D ≤ n^(3*(J+1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hH : D+1 ≤ H := by dsimp [H];omega
  have hD : (2:ℚ) ≤ D := by exact_mod_cast hn.trans dn
  have hp : (2:ℚ) ≤ n := by exact_mod_cast hn
  have hg' : gap D H ≤ 1 := by
    exact hg.trans (by apply div_le_one_of_le₀ <;> have := (Nat.cast_nonneg J : (0:ℚ) ≤ J) <;> linarith)
  have hgram := (NymanBeurling.polynomial_cutoff_rational_gram_criterion.2.1 D H hH)
  obtain ⟨c,_,he,hc⟩ := hgram.2.2.2
  refine ⟨c,he.le.trans hg,?_⟩
  have hm : 2*(D+2:ℚ)^2+36*(D+1:ℚ)^3*gap D H ≤ 296*(D:ℚ)^3 := by
    calc
      _ ≤ 2*(2*D:ℚ)^2+36*(2*D:ℚ)^3*1 := by gcongr <;> linarith
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg (D:ℚ)) (show 0 ≤ (D:ℚ)-1 by linarith)]
  have hfactor : (D:ℚ)^3=(n:ℚ)^3*(n:ℚ)^(3*(J+1)) := by
    dsimp [D];push_cast
    rw [←pow_mul,←pow_add];congr 1;omega
  have hh : (H:ℚ)=512*(n:ℚ)^(3*(J+1)) := by dsimp [H];push_cast;rfl
  have hden : 0 < (n:ℚ)^(3*(J+1)) := by positivity
  have ht : (2*(D+2:ℚ)^2+36*(D+1:ℚ)^3*gap D H)/(H+1:ℚ) ≤ 296*(n:ℚ)^3/512 := by
    calc
      _ ≤ 296*(D:ℚ)^3/(H+1:ℚ) := by gcongr
      _ ≤ 296*(D:ℚ)^3/(H:ℚ) := by apply div_le_div_of_nonneg_left (by positivity) (by rw [hh];positivity);linarith
      _ = _ := by rw [hfactor,hh];field_simp
  have hn3 : (8:ℚ) ≤ (n:ℚ)^3 := by
    calc
      8=(2:ℚ)^3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp 3
  have hcost : cost c H ≤ (n:ℚ)^3 := by linarith only [hc,hg',ht,hn3]
  have hpos : 0 ≤ cost c H := by unfold cost headEnergy;positivity
  calc
    (cost c H)^(J+1) ≤ ((n:ℚ)^3)^(J+1) := pow_le_pow_left₀ hpos hcost _
    _ ≤ (H+1:ℚ) := by rw [←pow_mul,hh];linarith
end SubcubicCertificate

theorem NymanBeurling.subpower_remainder_certificates (J L : ℕ) :
  ∃ (H K : ℕ) (c : ℕ→₀ℚ), L≤H ∧ (
    let R := fun n : ℕ => 1-∑ k∈c.support,c k*((((n+1)%(k+2):ℕ):ℚ)/(k+2:ℚ))
    let E := fun n : ℕ => ((R n)^2/((n+1:ℚ)*(n+2:ℚ)):ℚ)
    let C : ℚ := (∑ n∈Finset.range K,E n)+(1+∑ k∈c.support,|c k|)^2/(K+1:ℚ)
    (∑ n∈Finset.range H,E n)≤1/(J+1:ℚ) ∧ C^(J+1)≤(H+1:ℚ))  := by
  obtain ⟨n,hn,hg⟩ := NymanBeurling.cofinal_subcubic_rational_gram_rows J L
  have hn' := (le_max_left 2 L).trans hn
  obtain ⟨c,hp,hc⟩ := SubcubicCertificate.budget hn' hg
  let H := 512*n^(3*(J+1))
  have hL : L ≤ H := calc
    L ≤ n := (le_max_right 2 L).trans hn
    _ ≤ n^(3*(J+1)) := Nat.le_self_pow (by omega) _
    _ ≤ H := by dsimp [H];omega
  refine ⟨H,H,c,hL,?_⟩
  simpa only [H, NymanBeurling.RationalGram.cost,headEnergy,NymanBeurling.RationalGram.residual,mass,
    Nat.cast_add,Nat.cast_ofNat,mul_div_assoc] using And.intro hp hc

end

-- Step 2: `NymanBeurling.subpower_remainder_certificates` implies `MasulloRH.zero_free_right` (accepted reduction of `MasulloRH.zero_free_right`).
section

open Filter Topology

private theorem cost_root {x y : ℝ} (hx : 0≤x) {n : ℕ} (hn : 0<n) (h : x^n≤y) :
    x≤y^(1/(n:ℝ)) := by
  have h' := Real.rpow_le_rpow (pow_nonneg hx n) h (by positivity : 0≤1/(n:ℝ))
  simpa only [one_div,Real.pow_rpow_inv_natCast hx hn.ne'] using h'

theorem MasulloRH.zero_free_right (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  let b := 2*s.re-1
  let V := ‖s‖^2
  have hb : 0<b := by dsimp [b];linarith
  have hV : 0≤V := sq_nonneg _
  let p := min (b/2) (b/(4*(V+1)))
  have hp : 0<p := lt_min (by positivity) (by positivity)
  obtain ⟨J,hJ⟩ := exists_nat_gt (1/p)
  let d := 1/(J+1:ℝ)
  have hd : 0<d := by dsimp [d];positivity
  have hdp : d<p := by
    apply (div_lt_iff₀' (by positivity : 0<(J+1:ℝ))).mpr
    have hJ' := (div_lt_iff₀ hp).mp hJ
    nlinarith
  have hdb : d<b := by linarith [hdp.trans_le (min_le_left _ _)]
  have hVd : 4*V*d<b := by
    have h := (lt_div_iff₀ (by positivity : 0<4*(V+1))).mp (hdp.trans_le (min_le_right _ _))
    nlinarith
  have hlim : Tendsto (fun n : ℕ => (n+1:ℝ)^(-(b-d))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hdb)).comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hd))
  obtain ⟨H,K,c,hH,hP,hC⟩ := NymanBeurling.subpower_remainder_certificates J L
  let R := fun n : ℕ => 1-∑ k∈c.support,c k*((((n+1)%(k+2):ℕ):ℚ)/(k+2:ℚ))
  let E := fun n : ℕ => ((R n)^2/((n+1:ℚ)*(n+2:ℚ)):ℚ)
  let P : ℚ := ∑ n∈Finset.range H,E n
  let C : ℚ := (∑ n∈Finset.range K,E n)+(1+∑ k∈c.support,|c k|)^2/(K+1:ℚ)
  change P≤1/(J+1:ℚ) at hP
  change C^(J+1)≤(H+1:ℚ) at hC
  have hp' : (P:ℝ)≤d := by simpa only [d,Rat.cast_div,Rat.cast_add,Rat.cast_one,Rat.cast_natCast] using (Rat.cast_le (K:=ℝ)).mpr hP
  have epos (n : ℕ) : 0≤E n := by dsimp [E];positivity
  have ppos : 0≤(P:ℝ) := by exact_mod_cast (Finset.sum_nonneg (s:=Finset.range H) fun i _ => epos i)
  have cpos : 0≤(C:ℝ) := by
    have hsum := Finset.sum_nonneg (s:=Finset.range K) fun i _ => epos i
    have : 0≤C := by dsimp only [C];positivity
    exact_mod_cast this
  let x := (H+1:ℝ)
  have hx : 0<x := by dsimp [x];positivity
  have hc : (C:ℝ)≤x^d := by
    have h := cost_root cpos (n:=J+1) (by omega) (y:=x) (by simpa only [x,Rat.cast_pow,Rat.cast_add,Rat.cast_one,Rat.cast_natCast] using (Rat.cast_le (K:=ℝ)).mpr hC)
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have htail : x^(-b)*((C:ℝ)-(P:ℝ))≤d := by
    calc _ ≤ x^(-b)*x^d := mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hx.le _)
         _ = x^(-(b-d)) := by rw [←Real.rpow_add hx];congr 1;ring
         _ ≤ d := (hL H hH).le
  have h := (NymanBeurling.localized_zero_obstruction s hs hs_one hz c H K).2.2
  change b ≤ 2*V*((∑ n∈Finset.range H,(E n:ℝ))+x^(1-2*s.re)*((C:ℝ)-(∑ n∈Finset.range H,(E n:ℝ)))) at h
  have pcast : (∑ n∈Finset.range H,(E n:ℝ))=(P:ℝ) := by simp [P]
  rw [pcast,show 1-2*s.re= -b by dsimp [b];ring] at h
  have hh := mul_le_mul_of_nonneg_left (add_le_add hp' htail) (by linarith : 0≤2*V)
  linarith

end

-- Step 3: `MasulloRH.zero_free_right` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis := by
  have hright : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
    fun s hs hs1 => MasulloRH.zero_free_right s hs hs1
  refine riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => ?_)
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hneg : ∀ n : ℕ, s ≠ -(n : ℂ) := fun n h => by
      have hre := congrArg Complex.re h
      simp at hre
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hneg hs1
    rw [hz, mul_zero] at hfe
    have hre : (1 / 2 : ℝ) < (1 - s).re := by simp; linarith
    have h1s : (1 - s) ≠ 1 := fun h => by
      have hre' := congrArg Complex.re h
      simp at hre'
      linarith
    exact hright (1 - s) hre h1s hfe
  · exact heq
  · exact absurd hz (hright s hgt hs1)

end
