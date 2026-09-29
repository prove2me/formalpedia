-- Prove2me | Theorems.Thm_AddMonoidHom_exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt
-- name    : AddMonoidHom.exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/390bfd89-83b4-56aa-8409-d4d2ed56e291
-- title:
--   Base change of additive duals for finite ℤₚ-modules
-- statement:
--   Let $p$ be a prime, let $P$ be an additive commutative group carrying a $\mathbb{Z}_p$-module structure which is module-finite over $\mathbb{Z}_p$, and let $B$ be a commutative ring equipped with a $\mathbb{Z}/p$-algebra structure. Here $P \to_+ \mathbb{Z}/p$ denotes the group of additive homomorphisms from $P$ to $\mathbb{Z}/p$, a $\mathbb{Z}/p$-module under the pointwise action on values, and $P \to_+ B$ the group of additive homomorphisms from $P$ to $B$, a $B$-module in the same pointwise way; $B \otimes_{\mathbb{Z}/p} (P \to_+ \mathbb{Z}/p)$ is a $B$-module through the left factor. The assertion is that there exists a $B$-linear equivalence
--   $$e \colon B \otimes_{\mathbb{Z}/p} (P \to_+ \mathbb{Z}/p) \;\xrightarrow{\ \sim\ }\; (P \to_+ B)$$
--   such that for all $b \in B$, all additive $\varphi \colon P \to \mathbb{Z}/p$ and all $x \in P$ one has $e(b \otimes \varphi)(x) = b \cdot \mathrm{algebraMap}_{\mathbb{Z}/p, B}(\varphi(x))$, i.e. $e$ is the canonical base-change map, normalised on elementary tensors by multiplying $b$ with the image of $\varphi(x)$ under the structure morphism $\mathbb{Z}/p \to B$. Only existence together with this formula on elementary tensors is asserted; no further canonicity is claimed.
--
--   This is the statement that forming the $\mathbb{F}_p$-dual of a finitely generated $\mathbb{Z}_p$-module commutes with base change to an arbitrary commutative $\mathbb{F}_p$-algebra, additive homomorphisms being used in place of linear ones. It serves to pass from $\mathbb{F}_p$-coefficients to coefficients in a larger $\mathbb{F}_p$-algebra, and is cited in the construction of an injection whose image is the dual of a multiplicative submodule of the Tate module attached to a modular Jacobian in the ordinary case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem AddMonoidHom.exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt
    (p : ℕ) [Fact p.Prime] (P : Type*) [AddCommGroup P] [Module ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (B : Type*) [CommRing B] [Algebra (ZMod p) B] :
    ∃ e : B ⊗[ZMod p] (P →+ ZMod p) ≃ₗ[B] (P →+ B),
      ∀ (b : B) (φ : P →+ ZMod p) (x : P), e (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x) := by sorry
