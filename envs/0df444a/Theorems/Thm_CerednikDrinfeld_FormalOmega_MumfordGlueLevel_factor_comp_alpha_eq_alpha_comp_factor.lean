-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_alpha_eq_alpha_comp_factor
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueLevel.factor_comp_alpha_eq_alpha_comp_factor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/283d86c4-67d4-5817-84d3-39580228064f
-- title:
--   Reduction commutes with edge-chart transports
-- statement:
--   Fix a prime $r$ and a commutative domain $\mathcal O$, assumed (as an explicit hypothesis) to be a discrete valuation ring, together with an irreducible element $\pi \in \mathcal O$ such that the residue ring $\mathcal O/(\pi)$ has exactly $r$ elements, and a field $K_0$ that is an $\mathcal O$-algebra and a fraction field of $\mathcal O$. Let $g_1 \in GL_2(K_0)$ have underlying matrix $\operatorname{diag}(\pi,1)$, let $N$ be a subgroup of $PGL(2,K_0)$ and let $n$ be a natural number. Let $L$ be a Mumford gluing datum of level $n$ and $L'$ one of level $n+1$ for the parameters $(\mathcal O,\pi,K_0,r,g_1,N)$: each consists of a flat separated scheme over $\operatorname{Spec}(\mathcal O/(\pi^{m+1}))$ covered by finitely many open immersions from $\operatorname{Spec}$ of the truncated edge-chart ring $A_m = \mathrm{chartERing}(\mathcal O,\pi,r)/(\pi^{m+1})$, indexed $N$-invariantly by $GL_2(K_0)$, together with the localisation map $\iota$ to the truncated vertex-chart ring, the vertex transports $\tau$ and the edge-chart transports $\alpha$, which attach to each element of $GL_2(K_0)$ an $\mathcal O$-algebra self-map of $A_m$. Let $g \in GL_2(K_0)$ either fix both the standard vertex of the lattice tree and its translate by $g_1$, or interchange the two. The conclusion is the equality of ring homomorphisms $A_{n+1} \to A_n$ obtained by composing the reduction $A_{n+1} \to A_n$ (the map induced by $(\pi^{n+2}) \subseteq (\pi^{n+1})$) after $L'.\alpha\,g$, and by composing $L.\alpha\,g$ after that reduction.
--
--   This is the level-by-level compatibility of the edge-chart transports in a tower of Mumford gluing data: reduction modulo $\pi^{n+1}$ intertwines the transport at level $n+1$ with the transport at level $n$. It is used in [`CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition), where the reduced charts of a level-$(n+1)$ datum are fed to the chart-level characterisation at level $n$ in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_alpha_eq_alpha_comp_factor.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlueLevel.factor_comp_alpha_eq_alpha_comp_factor
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀))) (n : ℕ)
    (L : MumfordGlueLevel 𝒪 π K₀ r g₁ N n) (L' : MumfordGlueLevel 𝒪 π K₀ r g₁ N (n + 1))
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hg : (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
      (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀))) :
    (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1))))).comp (L'.α g).toAlgHom.toRingHom =
      (L.α g).toAlgHom.toRingHom.comp (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1))))) := by sorry
