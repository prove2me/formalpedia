-- Prove2me | Theorems.Thm_CuspForm_Bfam_levelBlock
-- name    : CuspForm.Bfam.levelBlock
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/004b011d-b638-53c5-b56e-13be1372dd60
-- title:
--   Level block for the chosen pairing family B
-- statement:
--   Let $\mathcal O$ be a commutative ring which is a local integral domain of characteristic zero, and let $p$ be a prime with $p \neq 2$ whose image in $\mathcal O$ is not a unit. The conclusion is the assertion that the family [`CuspForm.Bfam 𝒪`](def/CuspForm_CornerPairingFamily.html#L57) — the family of pairings selected by Hilbert's choice operator from those satisfying both [`CuspForm.Bfam.LevelBlock`](def/CuspForm_CornerPairingFamily.html#L19) and [`CuspForm.Bfam.DegeneracyBlock`](def/CuspForm_CornerPairingFamily.html#L36) — satisfies the first of these two blocks: for every nonzero level $M$, every subgroup $H \le (\mathbb Z/M)^\times$ and every level datum $h_1 : \mathrm{LevelLE}\ M\ M\ \top\ H\ 1$ (the divisibilities $M \mid M$ and $1 \mid M/M$ together with the condition that every $u \in H$ reduces into the full group), if the index $[(\mathbb Z/M)^\times : H]$ is a unit in $\mathcal O$ then, writing $W = W(M,H)$ for the $\mathcal O$-submodule of $H^1(\Gamma_H(M),\mathcal O) = \operatorname{Hom}(\Gamma_H(M),\mathcal O)$ obtained by applying the restriction map `iDegL M M ⊤ H 1` (precomposition with the inclusion-type map `iotaDeg` at degree $1$) to the parabolic submodule of $\operatorname{Hom}(\Gamma_0(M),\mathcal O)$, i.e. to those additive characters vanishing on every $\gamma$ with $\operatorname{tr}(\gamma)^2 = 4$, the following three statements hold: (i) the $\mathcal O$-linear map $W \to (W \to_{\mathcal O} \mathcal O)$ given by $B_{M,H}$ is bijective; (ii) for every nonzero $\ell$ which is prime or divides $M$, and all $x,y,T_x,T_y \in W$ whose underlying homomorphisms satisfy $T_x = T_\ell x$ and $T_y = T_\ell y$ for the transfer-defined operator `heckeT M H ℓ 𝒪`, one has $B_{M,H}(T_x,y) = B_{M,H}(x,T_y)$; (iii) for every $d \in (\mathbb Z/M)^\times$ the diamond operator `diamondL M H 𝒪 d` fixes every element of $W$. Here $\Gamma_H(M)$ is the subgroup of $\mathrm{SL}_2(\mathbb Z)$ image of the preimage of $H$ under the lower-right-entry character `gamma0Units` on $\Gamma_0(M)$.
--
--   This records that the pairing family fixed once and for all by [`CuspForm.Bfam`](def/CuspForm_CornerPairingFamily.html#L57) is, at levels of unit index, perfect, self-adjoint for the Hecke operators $T_\ell$ and $U_\ell$, and invariant under the diamond operators; classically it is the cup product on the parabolic cohomology of the modular curve twisted on one side by an Atkin–Lehner involution. It is used in the local analysis of the Hecke module $H^1$ at a maximal ideal, feeding the presentations of Hecke algebras and the corner-pairing data that go into the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_Bfam_levelBlock.lean

import Definitions.Def_CuspForm_CornerPairingFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier

theorem CuspForm.Bfam.levelBlock
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪)) :
    ∀ (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ H 1),
      IsUnit ((H.index : ℕ) : 𝒪) →
      Function.Bijective (CuspForm.Bfam 𝒪 M H h₁) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], (ℓ.Prime ∨ ℓ ∣ M) →
        ∀ (x y Tx Ty : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map
            (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
          (Tx : H1 M H 𝒪) = heckeT M H ℓ 𝒪 x → (Ty : H1 M H 𝒪) = heckeT M H ℓ 𝒪 y →
          CuspForm.Bfam 𝒪 M H h₁ Tx y = CuspForm.Bfam 𝒪 M H h₁ x Ty) ∧
      (∀ (d : (ZMod M)ˣ) (x : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map
            (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
          diamondL M H 𝒪 d (x : H1 M H 𝒪) = x) := by sorry
