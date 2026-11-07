-- Prove2me | Theorems.Thm_ApproxGKR_eq_C_5_sum_identity
-- name    : ApproxGKR.eq_C_5_sum_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:15.420376+00:00
-- url     : https://prove2.me/theorems/246c82dd-852d-4ff4-84a7-3416ef54764c
-- title:
--   (C.5)–(C.6) — the GKR sum identity for every extension agreeing on labels
-- statement:
--   Let $i<L$ and let $\widetilde{\mathrm{add}}_i,\widetilde{\mathrm{mult}}_i$ be any polynomials agreeing with the wiring predicates on $H^{m_i}\times H^{m_{i+1}}\times H^{m_{i+1}}$. Then:
--   1. for every gate label $g$ of layer $i$,
--   $$\sum_{u,v\in H^{m_{i+1}}}\Big[\widetilde{\mathrm{add}}_i(g,u,v)\big(\widetilde V_{i+1}(u)+\widetilde V_{i+1}(v)\big)+\widetilde{\mathrm{mult}}_i(g,u,v)\widetilde V_{i+1}(u)\widetilde V_{i+1}(v)\Big]=V_i(g);$$
--   2. for every points $\rho_0,\rho_1\in\mathbb C^{m_i}$ and coefficients $c_0,c_1\in\mathbb C$, with $\Psi_i=c_0\,\mathrm{eq}(\rho_0,\cdot)+c_1\,\mathrm{eq}(\rho_1,\cdot)$,
--   $$c_0\widetilde V_i(\rho_0)+c_1\widetilde V_i(\rho_1)=\sum_{g\in H^{m_i}}\sum_{u,v\in H^{m_{i+1}}}F_i(g,u,v),$$
--   $$F_i(g,u,v)=\Psi_i(g)\Big[\widetilde{\mathrm{add}}_i(g,u,v)\big(\widetilde V_{i+1}(u)+\widetilde V_{i+1}(v)\big)+\widetilde{\mathrm{mult}}_i(g,u,v)\widetilde V_{i+1}(u)\widetilde V_{i+1}(v)\Big].$$
--
--   This identity is what each layer's sum-check verifies; it needs no degree or norm bound on the extensions.
--
--   Differences from the source:
--   - generalization: claim points on the unit torus and coefficients (1, 0) or (1, λ) → arbitrary points ρ₀, ρ₁ ∈ ℂ^{m_i} and coefficients c₀, c₁ ∈ ℂ; reason: the identity is algebraic; the page's points and coefficients are a special case
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.1, eqs. (C.5)–(C.6), p.31

import Mathlib
import Definitions.Def_ApproxGKR_LayeredCircuit

namespace ApproxGKR

/-- **Equations (C.5)–(C.6): the GKR sum identity** (p.31).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.1, p.31: "Substituting the gate operations yields
`Ti = Σ_{g∈H^{mi}} Σ_{u,v∈H^{mi+1}} Fi(g, u, v)`" with
`Fi(g,u,v) = Ψi(g)[add~i(g,u,v)(Ṽi+1(u) + Ṽi+1(v)) + mult~i(g,u,v)Ṽi+1(u)Ṽi+1(v)]`; "For a fixed
parent label `g`, the wiring predicates are zero unless `u` and `v` are the children of `g`";
"this identity holds for every extension of the wiring predicates that agrees with them on
labels."

For a layer `i < L`, any two polynomials `add~ᵢ`, `mult~ᵢ` agreeing with the wiring predicates on
the grid, every gate label `g`, and every points `ρ₀, ρ₁ ∈ ℂ^{mᵢ}` and coefficients `c₀, c₁ ∈ ℂ`:
1. `Σ_{u,v} [add~ᵢ(g,u,v)(Ṽᵢ₊₁(u) + Ṽᵢ₊₁(v)) + mult~ᵢ(g,u,v)Ṽᵢ₊₁(u)Ṽᵢ₊₁(v)] = Vᵢ(g)`;
2. `c₀Ṽᵢ(ρ₀) + c₁Ṽᵢ(ρ₁) = Σ_g Σ_{u,v} Fᵢ(g,u,v)` with `Ψᵢ = c₀ eq(ρ₀,·) + c₁ eq(ρ₁,·)`.

**Formalization Note** No degree or norm condition on the extensions is needed, as the page
says. -/
theorem eq_C_5_sum_identity (C : LayeredCircuit) (x : InputList) (ext : ExtFamily C) (i : ℕ)
    (hi : i < C.L)
    (hagree : ∀ (ty : GateType) (g : C.Label i) (u v : C.Label (i + 1)),
      MvPolynomial.eval (wirePoint C g u v) (ext i ty) = wire C i ty g u v)
    (ρ0 ρ1 : Fin (C.m i) → ℂ) (c0 c1 : ℂ) :
    (∀ g : C.Label i,
      ∑ u : C.Label (i + 1), ∑ v : C.Label (i + 1),
        (MvPolynomial.eval (wirePoint C g u v) (ext i GateType.add) *
            (MvPolynomial.eval (labelPoint u) (Vt C x (i + 1)) +
              MvPolynomial.eval (labelPoint v) (Vt C x (i + 1))) +
          MvPolynomial.eval (wirePoint C g u v) (ext i GateType.mult) *
            (MvPolynomial.eval (labelPoint u) (Vt C x (i + 1)) *
              MvPolynomial.eval (labelPoint v) (Vt C x (i + 1)))) = value C x i g) ∧
    c0 * MvPolynomial.eval ρ0 (Vt C x i) + c1 * MvPolynomial.eval ρ1 (Vt C x i) =
      ∑ g : C.Label i, ∑ u : C.Label (i + 1), ∑ v : C.Label (i + 1),
        MvPolynomial.eval (labelPoint g) (Psi C.h ρ0 ρ1 c0 c1) *
          (MvPolynomial.eval (wirePoint C g u v) (ext i GateType.add) *
              (MvPolynomial.eval (labelPoint u) (Vt C x (i + 1)) +
                MvPolynomial.eval (labelPoint v) (Vt C x (i + 1))) +
            MvPolynomial.eval (wirePoint C g u v) (ext i GateType.mult) *
              (MvPolynomial.eval (labelPoint u) (Vt C x (i + 1)) *
                MvPolynomial.eval (labelPoint v) (Vt C x (i + 1)))) := by sorry

end ApproxGKR
