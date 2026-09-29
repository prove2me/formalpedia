-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow
-- name    : CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/2b29ac94-ce11-5c26-a6a8-dc2d8bf0fdcd
-- title:
--   Transport of an endomorphism embedding along a quasi-invertible isogeny
-- statement:
--   Fix a prime $r$ and write $\mathcal O = W(\mathbb F_{r^2})$ for the Witt vectors of the field with $r^2$ elements, as used in the structure `FormalODModule r` (a two-dimensional commutative formal group law $F$ over the base, an additive and multiplicative action $a \mapsto \mathrm{act}(a)$ of $\mathcal O$ by endomorphism series with $\mathrm{act}(1)=\mathrm{id}$, and a series $\varpi$ with $\varpi\circ\varpi=\mathrm{act}(r)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\varphi(a))\circ\varpi$ for the Frobenius $\varphi$). Let $\kappa : k_0 \to k$ be an injective ring homomorphism of commutative rings, $X_0$ such a module over $k_0$, $\Phi$ one over $k$, and let $\beta_0,\beta_0'$ be pairs of power series in two variables over $k$ which are $\mathcal O_D$-homomorphisms (`IsODHom`: homomorphisms of the formal group laws commuting with all $\mathrm{act}(a)$ and with $\varpi$) from $\Phi$ to $X_0\otimes_\kappa k$ and back, satisfying $\beta_0'\circ\beta_0=\mathrm{act}_\Phi(r^N)$ and $\beta_0\circ\beta_0'=\mathrm{act}_{X_0\otimes k}(r^N)$ for some $N\in\mathbb N$, and assume that both $\beta_0$ and $\mathrm{act}_\Phi(r^N)$ are right-cancellable under substitution. Let $K_0$ be a field of characteristic zero and $E_0$ an injective ring homomorphism from the centralizer of $\{\mathrm{act}_\Phi(a)\}_a \cup \{\varpi_\Phi\}$ in $\mathrm{End}(\Phi.F)$ into $M_2(K_0)$. Then there is an injective ring homomorphism $E$ from the centralizer of $\{\mathrm{act}_{X_0}(a)\}_a\cup\{\varpi_{X_0}\}$ in $\mathrm{End}(X_0.F)$ into $M_2(K_0)$ such that for every $\varepsilon$ in that centralizer there is an element $e$ of the $\Phi$-centralizer whose power series equals $\beta_0'\circ(\kappa_*\varepsilon)\circ\beta_0$ and with $E_0(e) = r^N\cdot E(\varepsilon)$.
--
--   This is the transport step for embeddings of the $\mathcal O_D$-equivariant endomorphism ring of a special formal module into $2\times 2$ matrices: an embedding known for $\Phi$ is pushed along an isogeny $\beta_0$ admitting a quasi-inverse $\beta_0'$ with $\beta_0'\beta_0=[r^N]$, the scaling by $r^N$ recording the degree. It feeds the construction of such embeddings for modules isogenous to $\Phi$ and, through that, the endomorphism-algebra statements used in the Čerednik–Drinfeld description of fake elliptic curves and their fine moduli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow
    {r : ℕ} [Fact r.Prime]
    {k₀ k : Type} [CommRing k₀] [CommRing k] (κ : k₀ →+* k) (hκ : Function.Injective κ)
    (X₀ : FormalODModule r k₀) (Φ : FormalODModule r k)
    (β₀ β₀' : SpecialFormal.Series k) (N : ℕ)
    (hβ₀ : FormalODModule.IsODHom Φ (X₀.map κ) β₀) (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
    (h₁ : β₀'.comp β₀ = Φ.act ((r : Zp2 r) ^ N)) (h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N))
    (hc₁ : ∀ σ τ : SpecialFormal.Series k, σ.comp β₀ = τ.comp β₀ → σ = τ)
    (hc₂ : ∀ σ τ : SpecialFormal.Series k, σ.comp (Φ.act ((r : Zp2 r) ^ N)) = τ.comp (Φ.act ((r : Zp2 r) ^ N)) → σ = τ)
    {K₀ : Type} [Field K₀] [CharZero K₀]
    (E₀ : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀) :
    ∃ E : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀,
      Function.Injective E ∧
      ∀ ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})),
        ∃ e : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})),
          (e : MvFormalGroup.End Φ.F).toPowerSeries =
            β₀'.comp ((SpecialFormal.Series.map κ (ε : MvFormalGroup.End X₀.F).toPowerSeries).comp β₀) ∧
          E₀ e = ((r : K₀) ^ N) • E ε := by sorry
