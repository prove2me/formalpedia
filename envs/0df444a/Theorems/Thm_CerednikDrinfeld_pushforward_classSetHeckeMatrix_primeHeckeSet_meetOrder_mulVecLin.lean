-- Prove2me | Theorems.Thm_CerednikDrinfeld_pushforward_classSetHeckeMatrix_primeHeckeSet_meetOrder_mulVecLin
-- name    : CerednikDrinfeld.pushforward_classSetHeckeMatrix_primeHeckeSet_meetOrder_mulVecLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/84659ea0-d005-5607-b32a-8268dd3d7b96
-- title:
--   Hecke matrices commute with both class-set degeneracy push-forwards
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a $\mathbb{Z}$-submodule $R$ of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project: $1\in R$, $R$ is closed under multiplication, its $\mathbb{Q}$-span is everything, and it is finitely generated. Let $q,\ell$ be nonzero natural numbers with $\ell$ coprime to $q$, and let $n$ be a unit of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ lying in [`QuaternionAlgebra.primeHeckeSet R q`](def/QuaternionAlgebra_ClassSetHecke.html#L109), i.e. $n$ lies in the finite-adelic box of $R$, $q\,n^{-1}$ lies in that box, while $n^{-1}$ and $q^{-1}n$ do not. Write $S=$ [`CerednikDrinfeld.meetOrder R n`](def/CerednikDrinfeld_ClassSetGraph.html#L15) $= R\sqcap$ [`Submodule.conjByFiniteIdele R n`](def/Submodule_FiniteAdeleBox.html#L31), and let $\mathrm{Cl}(S)$, $\mathrm{Cl}(R)$ be the double coset quotients of the adelic unit group by the diagonal image of $\mathbb{H}[\mathbb{Q},a,b]^{\times}$ on the left and by the stabiliser of the finite-adelic box of $S$, respectively of $R$, on the right; these are assumed finite with decidable equality. Let $m$ be an adelic unit and $\tau$ a self-map of the adelic unit group such that either $m=1$ and $\tau=\mathrm{id}$, or $m=n$ and $\tau(h)=n^{-1}hn$; thus $m\in\{1,n\}$, and $\tau$ occurs in no other hypothesis and not in the conclusion. Let $x:\mathrm{Cl}(S)\to\mathbb{Z}$ and $v\in\mathrm{Cl}(R)$. Then the push-forward along $\pi_m:\mathrm{Cl}(S)\to\mathrm{Cl}(R)$, $e\mapsto[\,e.\mathrm{out}\cdot m\,]$ — that is, the linear map $(\pi_m)_*y\,(v)=\sum_{e,\ \pi_m(e)=v}y(e)$ — satisfies $$(\pi_m)_*\bigl(B_S\,x\bigr)(v)=\bigl(B_R\,(\pi_m)_*x\bigr)(v),$$ where $B_S$ and $B_R$ are the class-set Hecke matrices attached to the Hecke sets of $S$, respectively $R$, at $\ell$, whose $(i,j)$ entry is the cardinality of the Hecke incidence set of the chosen representative of $j$ against $i$, acting by matrix–vector multiplication.
--
--   This is the Hecke-equivariance (in Brandt matrix form) of the two degeneracy maps from the class set of $R\cap nRn^{-1}$ to that of $R$, at an index $\ell$ coprime to the level parameter $q$; classically it expresses that correspondences at good primes commute with the degeneracy push-forwards. It supplies the prime-to-$q$ branch used by [`CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne`](thm.html#CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne) in the construction of the class-set graph with its Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_pushforward_classSetHeckeMatrix_primeHeckeSet_meetOrder_mulVecLin.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.pushforward_classSetHeckeMatrix_primeHeckeSet_meetOrder_mulVecLin
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsOrder R) (q ℓ : ℕ)
    (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (hcop : ℓ.Coprime q) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)))]
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R))]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (τ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ → (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hmτ : (m = 1 ∧ τ = id) ∨ (m = n ∧ τ = fun h => n⁻¹ * h * n))
    (x : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) → ℤ) (v : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R)) :
    CerednikDrinfeld.pushforward
        (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m))
        ((CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n))
          (QuaternionAlgebra.primeHeckeSet (CerednikDrinfeld.meetOrder R n) ℓ)).mulVecLin x) v =
      (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer R) (QuaternionAlgebra.primeHeckeSet R ℓ)).mulVecLin
        (CerednikDrinfeld.pushforward
          (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m)) x) v := by sorry
