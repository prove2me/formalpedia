-- Prove2me | Theorems.Thm_CartierDual_isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange
-- name    : CartierDual.isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/1b4cd30c-29c3-52f0-bfbe-d72df85d4cea
-- title:
--   Locality of H and of H^D descends to the fibre over k₀
-- statement:
--   Let $p$ be a prime and write $\mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator (in lowest terms) is coprime to $p$. Let $H$ be a commutative ring carrying the structure of a Hopf algebra over $\mathbb{Z}_{(p)}$ which is finite and free as a $\mathbb{Z}_{(p)}$-module and whose comultiplication is cocommutative, and let $k_0$ be a field of characteristic $p$ equipped with a $\mathbb{Z}_{(p)}$-algebra structure. The conclusion is the conjunction of two implications. First: if $H$ is a local ring, then so is the base change $k_0 \otimes_{\mathbb{Z}_{(p)}} H$. Second: if the Cartier dual $\mathrm{CartierDual}\,\mathbb{Z}_{(p)}\,H$ — the $\mathbb{Z}_{(p)}$-module dual $\mathrm{Module.Dual}\,\mathbb{Z}_{(p)}\,H$ of $H$ with its ring structure coming from the Hopf structure on $H$ — is a local ring, then the Cartier dual $\mathrm{CartierDual}\,k_0\,(k_0 \otimes_{\mathbb{Z}_{(p)}} H)$ of the base change, formed over $k_0$, is a local ring as well.
--
--   In the language of group schemes this says that connectedness of a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$, and connectedness of its Cartier dual, are both inherited by the special fibre over an arbitrary field of characteristic $p$; equivalently, being local (connected) and having local Cartier dual (connected dual, i.e. unipotent-type behaviour) survive reduction. It is used in the Dieudonné-module part of the local study of finite flat group schemes, where statements about orders of kernels of Frobenius and Verschiebung and about the bottom layer of a group scheme are reduced to the fibre over a field of characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct in

theorem CartierDual.isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (k₀ : Type) [Field k₀] [CharP k₀ p] [Algebra (GaloisRep.ratLocalizedAt p) k₀] :
    (IsLocalRing H → IsLocalRing (k₀ ⊗[GaloisRep.ratLocalizedAt p] H)) ∧
      (IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H) →
        IsLocalRing (CartierDual k₀ (k₀ ⊗[GaloisRep.ratLocalizedAt p] H))) := by sorry
