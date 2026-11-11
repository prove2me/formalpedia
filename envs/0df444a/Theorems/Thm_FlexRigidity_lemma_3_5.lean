-- Prove2me | Theorems.Thm_FlexRigidity_lemma_3_5
-- name    : FlexRigidity.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:21:11.733052+00:00
-- url     : https://prove2.me/theorems/8884add2-f668-4a32-ad3c-67789d6c9be4
-- title:
--   Lemma 3.5 — replacer-channel chain rule
-- statement:
--   Let $1<\alpha<2$, let $\mathcal G\in\mathrm{CPTP}(M,ZSQ)$ have classical output $Z$, and let $\mathcal P\in\mathrm{CP}(ZSQ,ZSQ)$ be a controlled replacer of the form (16) (positive weights $a_z$ on $\mathcal Z^*$, positive definite replacement operators $\omega^z_S$ off $\mathcal Z^*$). For any CPTP map $\mathcal T$ set $\mathcal E=\mathcal T\circ\mathcal G$ and $\mathcal F=\mathcal T\circ\mathcal P\circ\mathcal G$. With $R\cong M$:
--
--   1. $D^{\mathrm{reg}}_\alpha(\mathcal E\otimes\mathrm{id}_R\|\mathcal F\otimes\mathrm{id}_R)\le D_{1/(2-\alpha)}(\mathcal G\otimes\mathrm{id}_R\|(\mathcal P\circ\mathcal G)\otimes\mathrm{id}_R)$;
--   2. for every finite reference $K$, normalized $\rho_{KM}$ and PSD $\sigma_{KM}$,
--   $$D_\alpha\big((\mathcal E\otimes\mathrm{id}_K)[\rho]\big\|(\mathcal F\otimes\mathrm{id}_K)[\sigma]\big)\le D_\alpha(\rho\|\sigma)+D_{1/(2-\alpha)}(\mathcal G\otimes\mathrm{id}_R\|(\mathcal P\circ\mathcal G)\otimes\mathrm{id}_R).$$
--
--   This chain rule drives the round-by-round induction in the proof of Theorem 4.4.
--
--   Differences from the source:
--   - encoding: P ∈ CP(ZSQ, ZSQ) of the form (16), specified on Z-classical inputs → ctrlReplacer, which pinches Z and then acts as (16); reason: P is applied only after G, whose output is classical on Z, so P ∘ G and T ∘ P ∘ G are unchanged
--   - reading: "with any common reference register" → for every finite register K, E ⊗ id_K and F ⊗ id_K act on ρ_{KM} and σ_{KM}; reason: the reference is arbitrary and common to both arguments
--   - encoding: reference register R ≅ M → the reference is the type M itself, placed before the system register; reason: Lean convention; the same register up to the identification
--   - encoding: divergences and channel divergences with values in [0, +∞] → values in EReal (extended reals); reason: Lean convention; the +∞ conventions of Definition 2.7 are kept, no instance changes
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 3.5, p. 26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_regChanDiv
import Definitions.Def_FlexRigidity_ctrlReplacer
import Definitions.Def_FlexRigidity_HasClassicalFirst
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 3.5 (Replacer-channel chain rule)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 26). Let `1 < α < 2`, let `G ∈ CPTP(M, ZSQ)` have
classical output `Z`, and let `P ∈ CP(ZSQ, ZSQ)` have the form (16). For any CPTP map `T`, set
`E = T ∘ G` and `F = T ∘ P ∘ G`. With `R ≅ M`,
`D^reg_α(E ⊗ id_R‖F ⊗ id_R) ≤ D_{1/(2−α)}(G ⊗ id_R‖(P ∘ G) ⊗ id_R)`.
Consequently, for normalized `ρ` and PSD `σ`, with any common reference register `K`,
`D_α(E[ρ]‖F[σ]) ≤ D_α(ρ‖σ) + D_{1/(2−α)}(G ⊗ id_R‖(P ∘ G) ⊗ id_R)`.

**Formalization Note** `P` is the controlled replacer `ctrlReplacer Zs a ω` with `a_z > 0` on
`Z*` and positive definite `ω^z` off `Z*`; it pinches `Z` first, which agrees with (16) on the
`Z`-classical outputs of `G`. In the second claim `E[ρ]` is `(E ⊗ id_K)[ρ_{KM}]`. -/
theorem lemma_3_5 {M Z S Q N : Type} [Fintype M] [DecidableEq M] [Fintype Z] [DecidableEq Z]
    [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] [Fintype N] [DecidableEq N]
    (α : ℝ) (hα : 1 < α ∧ α < 2) (G : Superop M (Z × S × Q)) (hG : IsChannel G)
    (hGc : HasClassicalFirst G) (Zs : Finset Z) (a : Z → ℝ) (ω : Z → Matrix S S ℂ)
    (ha : ∀ z ∈ Zs, 0 < a z) (hω : ∀ z ∉ Zs, (ω z).PosDef)
    (T : Superop (Z × S × Q) N) (hT : IsChannel T) :
    let P := ctrlReplacer (Q := Q) Zs a ω
    let E : Superop M N := fun X => T (G X)
    let F : Superop M N := fun X => T (P (G X))
    regChanDiv α (idTensorSuperop (R := M) E) (idTensorSuperop (R := M) F) ≤
        chanDiv (1 / (2 - α)) (idTensorSuperop (R := M) G)
          (idTensorSuperop (R := M) (fun X => P (G X))) ∧
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ρ σ : Matrix (K × M) (K × M) ℂ),
      Density ρ → σ.PosSemidef →
      divergence α (idTensorSuperop (R := K) E ρ) (idTensorSuperop (R := K) F σ) ≤
        divergence α ρ σ + chanDiv (1 / (2 - α)) (idTensorSuperop (R := M) G)
          (idTensorSuperop (R := M) (fun X => P (G X))) := by sorry

end FlexRigidity
