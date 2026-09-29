-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField
-- name    : ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/ed3cd72a-5358-5cdf-b2f9-6a0de613e739
-- title:
--   Tame local 𝔽ₚ[Δ]-dimension count for K_w^×/(K_w^×)ᵖ
-- statement:
--   Fix a prime $p$ and work inside a fixed algebraic closure $\overline{\mathbb{Q}}_p$ (`PadicAlgCl p`). Let $K$ be an intermediate field of $\overline{\mathbb{Q}}_p/\mathbb{Q}_p$ that is finite-dimensional over $\mathbb{Q}_p$, and let $K_w$ be an intermediate field of $\overline{\mathbb{Q}}_p/K$ that is finite-dimensional and Galois over $K$, with $p \nmid [K_w:K]$ (tameness). Write $\Delta = K_w \simeq_{\mathrm{alg}[K]} K_w$ for the Galois group. Let $V_N$ be a finite-dimensional $\mathbb{Z}/p$-vector space carrying a representation $N$ of $\Delta$. Let $V_{PF}$ carry a representation $PF$ together with a surjective additive map $\pi_F \colon \mathrm{Additive}\,K_w^\times \to V_{PF}$ whose kernel consists exactly of the $p$-th powers ($\pi_F(u) = 0$ iff $u = w^p$ for some unit $w$) and which is $\Delta$-equivariant, $\pi_F(\sigma u) = PF(\sigma)\,\pi_F(u)$; thus $V_{PF}$ presents $K_w^\times/(K_w^\times)^p$. Let $V_{TF}$ carry a representation $TF$ together with an injective additive map $\iota_F \colon V_{TF} \to \mathrm{Additive}\,K_w^\times$ whose image is exactly $\{u : u^p = 1\}$ and which is $\Delta$-equivariant, $\iota_F(TF(\sigma)v) = \sigma(\iota_F v)$; thus $V_{TF}$ presents $\mu_p(K_w)$. Then the space of $\Delta$-invariants of $\mathrm{Hom}(V_N, V_{PF})$ (the `linHom` representation) has $\mathbb{Z}/p$-dimension $$[K:\mathbb{Q}_p]\cdot \dim V_N + \dim \mathrm{Hom}_\Delta(V_N, V_{TF}) + \dim \mathrm{Hom}_\Delta(V_N, \mathbb{Z}/p),$$ the last term taken with respect to the trivial representation of $\Delta$ on $\mathbb{Z}/p$.
--
--   This is the dimension-count form of the classical $\mathbb{F}_p[\Delta]$-module identity $[K_w^\times/(K_w^\times)^p] = [K:\mathbb{Q}_p]\,[\mathbb{F}_p[\Delta]] + [\mu_p] + [\mathbb{F}_p]$ for a tamely ramified finite Galois extension $K_w/K$ of $p$-adic fields, stated for arbitrary presentations of the two relevant $\Delta$-modules rather than for specific quotient constructions. It feeds the local computation of the dimension of continuous $H^1$ in terms of invariants, a dual twist and a multiple of the local degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open Module

theorem ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (Kw : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K Kw] [IsGalois K Kw]
    (htame : ¬ p ∣ Module.finrank K Kw)
    {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
    (N : Representation (ZMod p) (Kw ≃ₐ[K] Kw) VN)
    {VPF : Type*} [AddCommGroup VPF] [Module (ZMod p) VPF] (PF : Representation (ZMod p) (Kw ≃ₐ[K] Kw) VPF)
    (πF : Additive (↥Kw)ˣ →+ VPF) (hπF : Function.Surjective πF)
    (hkerπF : ∀ u : (↥Kw)ˣ, πF (Additive.ofMul u) = 0 ↔ ∃ w : (↥Kw)ˣ, w ^ p = u)
    (hπFΔ : ∀ (σ : Kw ≃ₐ[K] Kw) (u : (↥Kw)ˣ),
      πF (Additive.ofMul (Units.map (σ : Kw →* Kw) u)) = PF σ (πF (Additive.ofMul u)))
    {VTF : Type*} [AddCommGroup VTF] [Module (ZMod p) VTF] (TF : Representation (ZMod p) (Kw ≃ₐ[K] Kw) VTF)
    (ιF : VTF →+ Additive (↥Kw)ˣ) (hιF : Function.Injective ιF)
    (hranιF : ∀ u : (↥Kw)ˣ, Additive.ofMul u ∈ Set.range ιF ↔ u ^ p = 1)
    (hιFΔ : ∀ (σ : Kw ≃ₐ[K] Kw) (v : VTF),
      Additive.toMul (ιF (TF σ v)) = Units.map (σ : Kw →* Kw) (Additive.toMul (ιF v))) :
    finrank (ZMod p) (N.linHom PF).invariants
      = Module.finrank ℚ_[p] K * finrank (ZMod p) VN + finrank (ZMod p) (N.linHom TF).invariants
        + finrank (ZMod p) (N.linHom (Representation.trivial (ZMod p) (Kw ≃ₐ[K] Kw) (ZMod p))).invariants := by sorry
