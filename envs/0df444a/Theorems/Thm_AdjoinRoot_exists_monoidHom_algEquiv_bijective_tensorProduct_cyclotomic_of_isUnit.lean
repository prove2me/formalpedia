-- Prove2me | Theorems.Thm_AdjoinRoot_exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit
-- name    : AdjoinRoot.exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/c91bf467-09a8-5555-9f64-d3be6eae931b
-- title:
--   Cyclotomic 𝒪-algebra as a (ℤ/m)^×-cover
-- statement:
--   Let $\mathcal O$ be a commutative ring, let $m$ be a natural number, and assume the image of $m$ in $\mathcal O$ is a unit. Write $\mathcal O' :=$ `AdjoinRoot (cyclotomic m 𝒪)`, the quotient of $\mathcal O[X]$ by the $m$-th cyclotomic polynomial over $\mathcal O$, and let $x :=$ `AdjoinRoot.root (cyclotomic m 𝒪)` be the class of $X$. The assertion is that there exists a monoid homomorphism $\tau$ from the unit group $(\mathbb Z/m)^\times$ to the group of $\mathcal O$-algebra automorphisms of $\mathcal O'$ such that, first, for every unit $a$ one has $\tau(a)(x) = x^{\,v(a)}$, where $v(a)$ is the canonical natural-number representative (`ZMod.val`) of the residue class underlying $a$; and, second, the map
--   $$\mathcal O' \otimes_{\mathcal O} \mathcal O' \longrightarrow \bigl((\mathbb Z/m)^\times \to \mathcal O'\bigr), \qquad z \longmapsto \bigl(\mu(( \mathrm{id} \otimes \tau(\sigma))(z))\bigr)_{\sigma},$$
--   is bijective, where $\mu$ is the multiplication map `Algebra.TensorProduct.lmul'` of $\mathcal O'$ on $\mathcal O' \otimes_{\mathcal O} \mathcal O'$; on pure tensors this sends $s \otimes t$ to the family $(s\,\tau(\sigma)(t))_{\sigma}$. Bijectivity is asserted for the underlying function, the target being the function type indexed by $(\mathbb Z/m)^\times$, i.e. the product of copies of $\mathcal O'$.
--
--   This is the statement that, when $m$ is invertible in $\mathcal O$, the extension $\mathcal O \to \mathcal O[X]/(\Phi_m)$ is a Galois covering with group $(\mathbb Z/m)^\times$, the automorphisms being $x \mapsto x^{a}$ and the Galois condition being given in its split-tensor-product form $\mathcal O' \otimes_{\mathcal O} \mathcal O' \cong \prod_{(\mathbb Z/m)^\times} \mathcal O'$. It is used by [`Algebra.exists_cyclotomic_galois_cover_of_isUnit`](thm.html#Algebra.exists_cyclotomic_galois_cover_of_isUnit), which packages the cyclotomic cover in the form required later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdjoinRoot_exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial TensorProduct

universe u

theorem AdjoinRoot.exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit
    (𝒪 : Type u) [CommRing 𝒪] (m : ℕ) (hm : IsUnit ((m : ℕ) : 𝒪)) :
    ∃ τ : (ZMod m)ˣ →* (AdjoinRoot (cyclotomic m 𝒪) ≃ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)),
      (∀ a : (ZMod m)ˣ, τ a (AdjoinRoot.root (cyclotomic m 𝒪)) = AdjoinRoot.root (cyclotomic m 𝒪) ^ (a : ZMod m).val) ∧
      Function.Bijective fun x : AdjoinRoot (cyclotomic m 𝒪) ⊗[𝒪] AdjoinRoot (cyclotomic m 𝒪) => fun σ : (ZMod m)ˣ =>
        Algebra.TensorProduct.lmul' (S := AdjoinRoot (cyclotomic m 𝒪)) 𝒪
          (Algebra.TensorProduct.map (AlgHom.id 𝒪 (AdjoinRoot (cyclotomic m 𝒪)))
            ((τ σ : AdjoinRoot (cyclotomic m 𝒪) ≃ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)) :
              AdjoinRoot (cyclotomic m 𝒪) →ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)) x) := by sorry
