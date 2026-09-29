-- Prove2me | Theorems.Thm_AutomorphicForm_HeckeEigensystem_cNorm_eq_of_asIdeal_eq_smul
-- name    : AutomorphicForm.HeckeEigensystem.cNorm_eq_of_asIdeal_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/40b98d65-7992-530c-8796-7dae56319d21
-- title:
--   Galois-conjugate primes have equal absolute norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $w, w'$ be points of the height-one spectrum of the ring of integers $\mathcal{O}_L$, i.e. nonzero prime ideals of $\mathcal{O}_L$. Assume that the prime ideal underlying $w'$ equals the image of the prime ideal underlying $w$ under the pointwise action of $\sigma$ on ideals of $\mathcal{O}_L$, that is $\mathfrak{p}_{w'} = \sigma \cdot \mathfrak{p}_{w}$. The conclusion is that the complex numbers $\mathrm{cNorm}\,w'$ and $\mathrm{cNorm}\,w$ agree, where for a finite place $v$ the quantity [`AutomorphicForm.HeckeEigensystem.cNorm`](def/AutomorphicForm_ArithCuspRealization.html#L15) $v$ is by definition the absolute ideal norm $\mathrm{absNorm}(\mathfrak{p}_v) = [\mathcal{O}_L : \mathfrak{p}_v]$, a natural number, viewed in $\mathbb{C}$. So the residue cardinality attached to a finite place of $L$ is unchanged under the Galois-type action of $\mathrm{Aut}_K(L)$ on primes.
--
--   This is the standard invariance of the absolute norm of a prime ideal under automorphisms of the ring of integers, recorded in the normalisation ($\mathrm{cNorm}$, i.e. the norm as a complex scalar) in which Hecke eigenvalue bookkeeping is carried out. It is used where local data at a place $w$ must be compared with the same data at a conjugate place $\sigma \cdot w$, in the statements about Hecke generators at places lying under a common place of the base field and in the asymptotic and moment estimates for automorphic forms that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_HeckeEigensystem_cNorm_eq_of_asIdeal_eq_smul.lean

import Definitions.Def_AutomorphicForm_ArithCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.HeckeEigensystem.cNorm_eq_of_asIdeal_eq_smul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) (h : w'.asIdeal = σ • w.asIdeal) :
    AutomorphicForm.HeckeEigensystem.cNorm w' = AutomorphicForm.HeckeEigensystem.cNorm w := by sorry
