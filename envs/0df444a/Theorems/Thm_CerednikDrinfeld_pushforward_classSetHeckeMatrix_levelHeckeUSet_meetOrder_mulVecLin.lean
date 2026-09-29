-- Prove2me | Theorems.Thm_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin
-- name    : CerednikDrinfeld.pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/59d3eda2-5375-5324-a9da-baf6803b2130
-- title:
--   Degeneracy push-forwards intertwine the U_ℓ class-set matrices
-- statement:
--   Let $a,b\in\mathbb Q$ and let $\Lambda,R$ be $\mathbb Z$-submodules of $\mathbb H[\mathbb Q,a,b]$ that are orders in the sense of [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11) (containing $1$, closed under multiplication, with $\mathbb Q$-span everything, and finitely generated), with $R\le\Lambda$. Let $q,\ell$ be non-zero naturals with $\ell$ coprime to $q$, and let $n$ be a unit of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q,f}$ lying in [`QuaternionAlgebra.primeHeckeSet R q`](def/QuaternionAlgebra_ClassSetHecke.html#L109), i.e. $n$ lies in the finite adele box $\widehat R$ of $R$, $q\,n^{-1}\in\widehat R$, while $n^{-1}\notin\widehat R$ and $q^{-1}n\notin\widehat R$. Put $S=$ [`CerednikDrinfeld.meetOrder R n`](def/CerednikDrinfeld_ClassSetGraph.html#L15) $=R\sqcap$ [`Submodule.conjByFiniteIdele R n`](def/Submodule_FiniteAdeleBox.html#L31), the elements of $R$ whose image under $x\mapsto nxn^{-1}$ lies in $\widehat R$; the class sets $\mathrm{Cl}(S)$, $\mathrm{Cl}(R)$ at the levels [`Submodule.finiteIdeleStabilizer`](def/Submodule_FiniteAdeleBox.html#L26) of $S$ and of $R$ (stabilisers of the respective finite adele boxes in the finite-adelic unit group) are assumed finite with decidable equality, $\mathrm{Cl}(U)$ being the double coset quotient of the image of the diagonal $\mathbb H[\mathbb Q,a,b]^\times$ by $U$. Let $m$ be a finite-adelic unit and $\tau$ a self-map of the finite-adelic units such that either $m=1$ and $\tau=\mathrm{id}$, or $m=n$ and $\tau(h)=n^{-1}hn$; only $m$ occurs in the conclusion. Let $x:\mathrm{Cl}(S)\to\mathbb Z$ and $v\in\mathrm{Cl}(R)$. Write $\pi_m:\mathrm{Cl}(S)\to\mathrm{Cl}(R)$ for $e\mapsto$ the class of $\tilde e\,m$, $\tilde e$ a chosen representative of $e$, and $(\pi_m)_*$ for the induced push-forward of $\mathbb Z$-valued functions, $(\pi_m)_*x\,(w)=\sum_{\pi_m(e)=w}x(e)$. For an order $O$ put $T_O=$ [`CerednikDrinfeld.levelHeckeUSet`](def/CerednikDrinfeld_ClassSetGraph.html#L44) $\Lambda\,O\,\ell$, the set of $h\in$ `primeHeckeSet O ℓ` with `conjByFiniteIdele O h` $\ne O$ and $O\not\le$ `conjByFiniteIdele Λ h`, and let the associated matrix on $\mathrm{Cl}(O)$ have $(i,j)$ entry `heckeKernel` at $(j,i)$, namely the cardinality of the incidence set `HeckeIncidence` for the level of $O$, $T_O$, a representative of $j$ and $i$. The assertion is that the matrix–vector products satisfy $(\pi_m)_*\bigl(T_S\cdot x\bigr)(v)=\bigl(T_R\cdot(\pi_m)_*x\bigr)(v)$.
--
--   This is the $U_\ell$-branch of the compatibility of class-set Hecke operators with the two degeneracy maps attached to an element $n$ of the Hecke set at $q$, for $\ell$ coprime to $q$; it is the analogue, for the level sets `levelHeckeUSet`, of the corresponding statement for prime Hecke sets. It is used in [`CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne`](thm.html#CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne), where the joint degeneracy map from edges to vertices is shown to intertwine the edge and vertex Hecke operators at primes away from $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin
    {a b : ℚ} (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hR : QuaternionAlgebra.IsOrder R)
    (hRΛ : R ≤ Λ) (q ℓ : ℕ)
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
          (CerednikDrinfeld.levelHeckeUSet Λ (CerednikDrinfeld.meetOrder R n) ℓ)).mulVecLin x) v =
      (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer R) (CerednikDrinfeld.levelHeckeUSet Λ R ℓ)).mulVecLin
        (CerednikDrinfeld.pushforward
          (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m)) x) v := by sorry
