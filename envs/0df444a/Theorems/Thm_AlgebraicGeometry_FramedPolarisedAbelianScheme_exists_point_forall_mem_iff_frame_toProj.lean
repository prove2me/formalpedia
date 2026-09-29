-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_point_forall_mem_iff_frame_toProj
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_point_forall_mem_iff_frame_toProj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/23e245e1-bfc5-52ac-a881-b2ef6074f1d7
-- title:
--   Hilbert point cutting out a framed polarised abelian scheme
-- statement:
--   Fix natural numbers $g, N, n$ and put $P := (N+1)t^{g} \in \mathbb{Q}[t]$. The hypothesis `hP` asks that $P$ be realised as an eventual Hilbert function in $N+1$ variables over some field: there are a field $K$ and an ideal $I \subseteq K[X_0,\dots,X_N]$ containing all homogeneous components of each of its elements, and a degree $d_1$, such that for every $d \ge d_1$ the $K$-dimension of `piece I d`, the quotient of the space of degree-$d$ homogeneous polynomials by its intersection with $I$, equals $P(d)$. The conclusion: there is $D$ such that for every $m \ge D$, every commutative ring $R$ and every `FramedPolarisedAbelianScheme g N n R` — a polarised abelian scheme $\mathrm{Xf}$ of relative fibre dimension $g$ over $R$ with $n$-torsion frame and invertible polarisation `pol` of geometric $h^0$ equal to $N+1$, equipped with a `ProjPresentation` `frame` of `pol` over $\mathrm{Proj}$ of $R[X_0,\dots,X_N]$ whose structural morphism `frame.toProj` is a closed immersion and whose sections `frame.σ` form a section basis over $\top$ — there exists a point $q$ of the Hilbert functor over $R$ in $\mathbb{P}^N$ with Hilbert function `hilbertFunctionOf N P m` (that is, a homogeneous ideal $q.I \subseteq R[X_0,\dots,X_N]$ all of whose graded pieces are finite projective $R$-modules with rank at each prime of $R$ equal to $\binom{N+d}{N}$ for $d < m$ and to $\lfloor P(d)\rfloor$ for $d \ge m$), such that for every $d \ge m$ and every homogeneous $F$ of degree $d$ one has $F \in q.I$ if and only if, for each $i \in \{0,\dots,N\}$, the section of the structure sheaf on the basic open set $D_+(X_i)$ determined by the degree-zero homogeneous localisation $F/X_i^{d}$ pulls back along `frame.toProj` to $0$ on the preimage of $D_+(X_i)$.
--
--   This is the step producing the Hilbert point of the closed subscheme $A \subseteq \mathbb{P}^N_R$ cut out by the frame of a polarised abelian scheme, the relevant Hilbert polynomial being $(N+1)t^{g}$ coming from $h^0(\mathcal{L}^{\otimes d}) = (N+1)d^{g}$ on geometric fibres; the characterisation of $q.I$ in degrees $\ge m$ identifies the ideal with the ideal of sections vanishing on $A$. It is used in the construction of the embedded representing object over Noetherian base rings, [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isImmersion_proj_represents_embedded_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_point_forall_mem_iff_frame_toProj.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor NeronModelInfra GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_point_forall_mem_iff_frame_toProj
    (g N n : ℕ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (N + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) =
        (Polynomial.C ((N : ℚ) + 1) * Polynomial.X ^ g).eval (d : ℚ)) :
    ∃ D : ℕ, ∀ m : ℕ, D ≤ m → ∀ (R : Type) [CommRing R] (Xf : FramedPolarisedAbelianScheme g N n R),
      ∃ q : Point R N (hilbertFunctionOf N (Polynomial.C ((N : ℚ) + 1) * Polynomial.X ^ g) m), ∀ (d : ℕ), m ≤ d →
        ∀ (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d),
          (F ∈ q.I ↔ ∀ i : Fin (N + 1),
            Xf.frame.toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (X i))
              ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (X i))
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0) := by sorry
