-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_tau_eq_tau_comp_factor
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueLevel.factor_comp_tau_eq_tau_comp_factor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/06a07e46-9caf-5d0d-8562-7654da41adcb
-- title:
--   Level compatibility of vertex-chart transports τ_g
-- statement:
--   Let $r$ be a prime, $\mathcal O$ a domain that is a discrete valuation ring (the hypothesis `hdvr`), $\pi \in \mathcal O$ irreducible with residue ring of cardinality $\operatorname{card}(\mathcal O/(\pi)) = r$, and $K_0$ a field that is a fraction field of $\mathcal O$. Let $g_1 \in \mathrm{GL}_2(K_0)$ be the matrix $\mathrm{diag}(\pi, 1)$, let $N \le \mathrm{PGL}(2,K_0)$ be a subgroup, let $n \in \mathbb N$, and let $L$ and $L'$ be Mumford gluing data for $(\mathcal O, \pi, K_0, r, g_1, N)$ of levels $n$ and $n+1$ respectively; among the components of such a datum is, for every $h \in \mathrm{GL}_2(K_0)$, an $\mathcal O$-algebra automorphism $\tau_h$ of the truncated vertex-chart ring $\mathrm{chartVRing}\,\mathcal O\, r / (\pi^{m+1})$, where $\mathrm{chartVRing}\,\mathcal O\,r$ is the localisation of $\mathcal O[X]$ away from $X^r - X$ and $m$ is the level. Finally let $g \in \mathrm{GL}_2(K_0)$ fix the standard vertex of the lattice tree, $\mathrm{Vertex.act}\ g\ (\mathrm{stdVertex}\ \mathcal O\ K_0) = \mathrm{stdVertex}\ \mathcal O\ K_0$. Then the two composites of ring homomorphisms from $\mathrm{chartVRing}\,\mathcal O\,r/(\pi^{n+2})$ to $\mathrm{chartVRing}\,\mathcal O\,r/(\pi^{n+1})$ agree: the level-$(n+1)$ automorphism $L'.\tau\ g$ followed by the reduction map induced by $(\pi^{n+2}) \subseteq (\pi^{n+1})$ equals that reduction map followed by the level-$n$ automorphism $L.\tau\ g$.
--
--   This is the compatibility, under reduction modulo one further power of $\pi$, of the transports of the standard vertex chart attached to elements of $\mathrm{GL}_2(K_0)$ stabilising the standard vertex, as required when the Mumford gluing data of successive levels are matched. It is used in the construction of transitions between levels, [`CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueLevel.exists_transition), and relies on the characterisation of $\tau_g$ by its effect on Deligne data of the formal upper half plane together with the existence result [`CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent`](thm.html#CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_factor_comp_tau_eq_tau_comp_factor.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlueLevel.factor_comp_tau_eq_tau_comp_factor
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀))) (n : ℕ)
    (L : MumfordGlueLevel 𝒪 π K₀ r g₁ N n) (L' : MumfordGlueLevel 𝒪 π K₀ r g₁ N (n + 1))
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg : Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀)) :
    (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (chartVRing 𝒪 r) π) (Nat.le_succ (n + 1))))).comp (L'.τ g).toAlgHom.toRingHom =
      (L.τ g).toAlgHom.toRingHom.comp (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (chartVRing 𝒪 r) π) (Nat.le_succ (n + 1))))) := by sorry
