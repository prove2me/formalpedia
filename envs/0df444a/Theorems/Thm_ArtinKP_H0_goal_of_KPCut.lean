-- Prove2me | Theorems.Thm_ArtinKP_H0_goal_of_KPCut
-- name    : ArtinKP.H0.goal_of_KPCut
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:04.883052+00:00
-- url     : https://prove2.me/theorems/4c9fa7b6-085b-4c60-b9ac-79c7677d2446
-- title:
--   ArtinKP.H0.goal_of_KPCut: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.H0`, with `open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots`, `open scoped Classical`, `open Classical in`):
--
--   ```lean
--   theorem goal_of_KPCut (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
--       (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
--       (h : KPCut n F ι) :
--     ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
--       ∀ (g : AllowedGen ι 𝔪),
--       let lsym : Ideal (𝓞 F) → F → ℂ := fun P t =>
--         if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
--             (yz.2 : F) * t = (yz.1 : F) then
--           sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
--         else 0
--       let ladd : Ideal (𝓞 F) → F → ℂ := fun P w =>
--         if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
--             yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
--             (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
--           sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
--         else 0
--       let Wv : Ideal (𝓞 F) → ℕ → ℂ := fun P e =>
--         if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
--         else if e % 3 = 1 then
--           (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
--         else 0
--       let Wsph : Ideal (𝓞 F) → ℤ → F → ℂ := fun P e₀ t =>
--         if e₀ < 0 then 0 else lsym P t ^ (2 * e₀.toNat) * Wv P e₀.toNat
--       let tau : Ideal (𝓞 F) → ℕ → ℂ := fun P j =>
--         ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
--           starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
--             sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))
--       let mask : (P : Ideal (𝓞 F)) → ℕ → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
--         fun P j v =>
--           if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
--           else (tau P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j
--       let Wweyl : (P : Ideal (𝓞 F)) → ℤ → F → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
--         fun P e₀ t v =>
--           if e₀ + 2 < 0 then 0 else
--             Wv P (e₀ + 2).toNat * lsym P t ^ (4 + 2 * (e₀ + 2).toNat) *
--               sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
--               ladd P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))
--       let Eloc : Ideal (𝓞 F) → ℕ → ℤ → F → ℂ := fun P k e₀ t =>
--         if k = 0 then Wsph P e₀ t else
--           ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
--             mask P (k % 6) v * (if v = 0 then Wsph P e₀ t else Wweyl P e₀ t v)
--       ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
--       ∃ (κ : ℝ → ℝ) (cκ Aκ α : ℝ), Measurable κ ∧ 0 < cκ ∧ 0 < Aκ ∧ 0 < α ∧ (∀ t, 0 ≤ κ t) ∧
--         (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
--           MellinConvergent (fun t => (κ t : ℂ)) s ∧
--           mellin (fun t => (κ t : ℂ)) s =
--             (cκ : ℂ) * (Aκ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6))) ∧
--         (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N))) ∧
--       ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
--       ∃ (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
--         (∀ c, Measurable (Fm c)) ∧ (∀ y, 0 ≤ bf y) ∧
--         (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
--         (∀ w c y, ContDiff ℝ 2 (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))) ∧
--         (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ w c y, ∀ j : ℕ, j ≤ 2 →
--           ‖iteratedDeriv j (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k))) 0‖ ≤
--             C * (∏ w', min (Real.exp (α * y.1 w')) (Real.exp (-(N * y.1 w')))) * bf y.2.2) ∧
--       ∀ 𝔟 : Ideal (𝓞 F), IsExterior 𝔪 𝔟 →
--       let fp : SModel 𝔪 k → ℂ := fun y =>
--         if y.2.2 = 0 then
--           ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)
--         else 0
--       let coef : RowClass 𝔪 → ℂ := fun z =>
--         residueSymbol ι 𝔪 𝔟 (rowElt g z) *
--           ∏ P ∈ (normalizedFactors z.1.1).toFinset,
--             Wsph P ((normalizedFactors z.1.1).count P : ℤ)
--               ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ)))
--       let Ez : RowClass 𝔪 → ℂ := fun z =>
--         (∏ P ∈ (normalizedFactors (z.1.1 * 𝔟)).toFinset,
--           Eloc P ((normalizedFactors 𝔟).count P)
--             (((normalizedFactors z.1.1).count P : ℤ) -
--               2 * ((normalizedFactors 𝔟).count P : ℤ))
--             ((rowElt g z : F) / (g.gen 𝔟 : F) ^ 2 *
--               (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
--                 2 * ((normalizedFactors 𝔟).count P : ℤ)))))
--       let D : SModel 𝔪 k → ℂ := fun y =>
--         (∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
--             coef p.1 * fp (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * (rowElt g p.1 : F)) + y)) -
--           ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
--             Ez p.1 * Fm (QuotientAddGroup.mk (sEmb 𝔪 k ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
--               (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)) - y)
--       ∀ (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) (y : SModel 𝔪 k),
--         D (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)) = D y
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.H0.KPCut` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinKPB017

section

namespace ArtinKP.H0

open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

open Classical in
theorem goal_of_KPCut (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (h : KPCut n F ι) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    let lsym : Ideal (𝓞 F) → F → ℂ := fun P t =>
      if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yz.2 : F) * t = (yz.1 : F) then
        sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
      else 0
    let ladd : Ideal (𝓞 F) → F → ℂ := fun P w =>
      if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
        sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
      else 0
    let Wv : Ideal (𝓞 F) → ℕ → ℂ := fun P e =>
      if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
      else if e % 3 = 1 then
        (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
      else 0
    let Wsph : Ideal (𝓞 F) → ℤ → F → ℂ := fun P e₀ t =>
      if e₀ < 0 then 0 else lsym P t ^ (2 * e₀.toNat) * Wv P e₀.toNat
    let tau : Ideal (𝓞 F) → ℕ → ℂ := fun P j =>
      ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
        starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
          sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))
    let mask : (P : Ideal (𝓞 F)) → ℕ → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P j v =>
        if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
        else (tau P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j
    let Wweyl : (P : Ideal (𝓞 F)) → ℤ → F → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P e₀ t v =>
        if e₀ + 2 < 0 then 0 else
          Wv P (e₀ + 2).toNat * lsym P t ^ (4 + 2 * (e₀ + 2).toNat) *
            sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
            ladd P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))
    let Eloc : Ideal (𝓞 F) → ℕ → ℤ → F → ℂ := fun P k e₀ t =>
      if k = 0 then Wsph P e₀ t else
        ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
          mask P (k % 6) v * (if v = 0 then Wsph P e₀ t else Wweyl P e₀ t v)
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ (κ : ℝ → ℝ) (cκ Aκ α : ℝ), Measurable κ ∧ 0 < cκ ∧ 0 < Aκ ∧ 0 < α ∧ (∀ t, 0 ≤ κ t) ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (κ t : ℂ)) s ∧
        mellin (fun t => (κ t : ℂ)) s =
          (cκ : ℂ) * (Aκ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N))) ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ c, Measurable (Fm c)) ∧ (∀ y, 0 ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
      (∀ w c y, ContDiff ℝ 2 (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k)))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ w c y, ∀ j : ℕ, j ≤ 2 →
        ‖iteratedDeriv j (fun s : ℝ => Fm c (y + ((Pi.single w s, 0, 0) : SModel 𝔪 k))) 0‖ ≤
          C * (∏ w', min (Real.exp (α * y.1 w')) (Real.exp (-(N * y.1 w')))) * bf y.2.2) ∧
    ∀ 𝔟 : Ideal (𝓞 F), IsExterior 𝔪 𝔟 →
    let fp : SModel 𝔪 k → ℂ := fun y =>
      if y.2.2 = 0 then
        ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)
      else 0
    let coef : RowClass 𝔪 → ℂ := fun z =>
      residueSymbol ι 𝔪 𝔟 (rowElt g z) *
        ∏ P ∈ (normalizedFactors z.1.1).toFinset,
          Wsph P ((normalizedFactors z.1.1).count P : ℤ)
            ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ)))
    let Ez : RowClass 𝔪 → ℂ := fun z =>
      (∏ P ∈ (normalizedFactors (z.1.1 * 𝔟)).toFinset,
        Eloc P ((normalizedFactors 𝔟).count P)
          (((normalizedFactors z.1.1).count P : ℤ) -
            2 * ((normalizedFactors 𝔟).count P : ℤ))
          ((rowElt g z : F) / (g.gen 𝔟 : F) ^ 2 *
            (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
              2 * ((normalizedFactors 𝔟).count P : ℤ)))))
    let D : SModel 𝔪 k → ℂ := fun y =>
      (∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
          coef p.1 * fp (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * (rowElt g p.1 : F)) + y)) -
        ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
          Ez p.1 * Fm (QuotientAddGroup.mk (sEmb 𝔪 k ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
            (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)) - y)
    ∀ (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) (y : SModel 𝔪 k),
      D (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)) = D y
  := by
  sorry

end ArtinKP.H0
end
