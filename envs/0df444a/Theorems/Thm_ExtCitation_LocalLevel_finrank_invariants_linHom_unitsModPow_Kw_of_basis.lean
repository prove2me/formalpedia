-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_Kw_of_basis
-- name    : ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_Kw_of_basis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/af4318ca-ca06-5df0-9972-f389584b2822
-- title:
--   Counting Δ-maps into K_w^×/(K_w^×)^q
-- statement:
--   Let $q$ be a prime and let $K_w$ be an intermediate field of the algebraic closure $\overline{\mathbb{Q}}_q$ over $\mathbb{Q}_q$ which is finite-dimensional over $\mathbb{Q}_q$; write $R_w$ for the valuation subring `Rw q Kw` of $K_w$, namely the pullback along $K_w \to \overline{\mathbb{Q}}_q$ of the valuation subring of the canonical valuation on $\overline{\mathbb{Q}}_q$. Let $\Delta$ be a finite group with $q \nmid |\Delta|$, and let $\mathrm{act} : \Delta \to \mathrm{Aut}_{\mathbb{Q}_q}(K_w)$ be a homomorphism. Let $\iota$ be a finite type and $w : \Delta \times \iota \to K_w$ a family with all values in $R_w$, linearly independent over $\mathbb{Q}_q$, with $|\Delta \times \iota| = \dim_{\mathbb{Q}_q} K_w$ (so $w$ is an integral $\mathbb{Q}_q$-basis), and permuted regularly in the first coordinate: $\mathrm{act}(d)\,w(d',i) = w(dd',i)$. Let $N$ be a representation of $\Delta$ on a finite-dimensional $\mathbb{Z}/q$-vector space $V_N$. Let $PF$ be a representation of $\Delta$ on a $\mathbb{Z}/q$-module $V_{PF}$ together with a surjective additive map $\pi_F : \mathrm{Additive}(K_w^\times) \to V_{PF}$ whose kernel is exactly the set of $q$-th powers and which intertwines the action of $\Delta$ on units with $PF$; thus $V_{PF} \cong K_w^\times/(K_w^\times)^q$ as $\mathbb{F}_q[\Delta]$-modules. Let $TF$ be a representation of $\Delta$ on $V_{TF}$ with an injective additive map $\iota_F : V_{TF} \to \mathrm{Additive}(K_w^\times)$ whose image is exactly the set of units $u$ with $u^q = 1$, again $\Delta$-equivariant; thus $V_{TF} \cong \mu_q(K_w)$. The conclusion is the dimension formula $$\dim_{\mathbb{F}_q} \mathrm{Hom}_\Delta(V_N, V_{PF}) = |\iota|\cdot \dim_{\mathbb{F}_q} V_N + \dim_{\mathbb{F}_q}\mathrm{Hom}_\Delta(V_N, V_{TF}) + \dim_{\mathbb{F}_q}\mathrm{Hom}_\Delta(V_N, \mathbb{F}_q),$$ where each $\mathrm{Hom}_\Delta$ is realised as the space of $\Delta$-invariants of the representation `Representation.linHom` on $\mathbb{Z}/q$-linear maps out of $V_N$, and the last term uses the trivial representation of $\Delta$ on $\mathbb{Z}/q$.
--
--   This is the relative form of the local count of $\mathbb{F}_q[\Delta]$-multiplicities in $K_w^\times/(K_w^\times)^q$ for a local field $K_w$ of residue characteristic $q$: any group of $\mathbb{Q}_q$-automorphisms of order prime to $q$ which permutes an integral basis regularly suffices, the index set $\iota$ playing the role of the degree of the subfield fixed by $\Delta$. It is used to derive the version stated for $\Delta = \mathrm{Gal}(K_w/K)$ of a Galois intermediate field, which feeds the local computations at primes above $q$ in the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_Kw_of_basis.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open Module

theorem ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_Kw_of_basis
    (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ) (act : Δ →* (Kw ≃ₐ[ℚ_[q]] Kw))
    {ι : Type*} [Fintype ι] (w : Δ × ι → Kw) (hwR : ∀ x, w x ∈ Rw q Kw) (hw : LinearIndependent ℚ_[q] w)
    (hcard : Fintype.card (Δ × ι) = Module.finrank ℚ_[q] Kw)
    (hperm : ∀ (d d' : Δ) (i : ι), act d (w (d', i)) = w (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)
    {VPF : Type*} [AddCommGroup VPF] [Module (ZMod q) VPF] (PF : Representation (ZMod q) Δ VPF)
    (πF : Additive (↥Kw)ˣ →+ VPF) (hπF : Function.Surjective πF)
    (hkerπF : ∀ u : (↥Kw)ˣ, πF (Additive.ofMul u) = 0 ↔ ∃ w : (↥Kw)ˣ, w ^ q = u)
    (hπFΔ : ∀ (d : Δ) (u : (↥Kw)ˣ),
      πF (Additive.ofMul (Units.map (act d : Kw →* Kw) u)) = PF d (πF (Additive.ofMul u)))
    {VTF : Type*} [AddCommGroup VTF] [Module (ZMod q) VTF] (TF : Representation (ZMod q) Δ VTF)
    (ιF : VTF →+ Additive (↥Kw)ˣ) (hιF : Function.Injective ιF)
    (hranιF : ∀ u : (↥Kw)ˣ, Additive.ofMul u ∈ Set.range ιF ↔ u ^ q = 1)
    (hιFΔ : ∀ (d : Δ) (v : VTF),
      Additive.toMul (ιF (TF d v)) = Units.map (act d : Kw →* Kw) (Additive.toMul (ιF v))) :
    finrank (ZMod q) (N.linHom PF).invariants
      = Fintype.card ι * finrank (ZMod q) VN + finrank (ZMod q) (N.linHom TF).invariants
        + finrank (ZMod q) (N.linHom (Representation.trivial (ZMod q) Δ (ZMod q))).invariants := by sorry
