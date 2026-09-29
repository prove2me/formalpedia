-- Prove2me | Theorems.Thm_CuspidalType_exists_semilinearMap_steinberg_quotient_forall_apply_eq_and_exists_basis_eq_of_steinberg_quotient_zmod
-- name    : CuspidalType.exists_semilinearMap_steinberg_quotient_forall_apply_eq_and_exists_basis_eq_of_steinberg_quotient_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/a6fd1e68-e776-5a2b-b53e-bdce2e2ed4a2
-- title:
--   Steinberg quotients over k descend to 𝔽ₚ, basis to basis
-- statement:
--   Let $q$ and $p$ be primes, put $G=\mathrm{GL}_2(\mathbb{Z}/q)$ ([`CuspidalType.GL2 q`](def/CuspidalType_IsCuspidalOfType.html#L19)) and let $P$ be the projectivisation of $(\mathbb{Z}/q)^2$ ([`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21)). For a field $F$, [`CuspidalType.ind q F`](def/CuspidalType_IsCuspidalOfType.html#L51) is the representation of $G$ on the finitely supported functions $P\to F$ by push-forward along the action of $g$, [`CuspidalType.steinberg q F`](def/CuspidalType_IsCuspidalOfType.html#L57) is its subrepresentation given by the kernel of the coefficient-sum map $\sum_x v(x)$, and [`CuspidalType.constFun q F`](def/CuspidalType_IsCuspidalOfType.html#L67) is the function with value $1$ at every point of $P$. The data are: a finite-dimensional $\mathbb{Z}/p$-vector space $W$ with a representation $\rho_W$ of $G$, a $\mathbb{Z}/p$-linear map $\pi_W$ from the kernel of the coefficient-sum map on $P\to_{\mathrm{f}}\mathbb{Z}/p$ to $W$ which is $G$-equivariant for $\rho_W$, surjective, and whose vanishing locus consists exactly of the scalar multiples $c\cdot\mathrm{constFun}$; and, for a field $k$ equipped with a $\mathbb{Z}/p$-algebra structure, a finite-dimensional $k$-vector space $V$ with a representation $\rho$ of $G$ and a $k$-linear map $\pi$ from the kernel of the coefficient-sum map on $P\to_{\mathrm{f}}k$ to $V$ with the same three properties. The conclusion asserts the existence of a map $j:W\to V$, semilinear along $\mathrm{algebraMap}\ (\mathbb{Z}/p)\ k$, satisfying $j(\rho_W(g)w)=\rho(g)(j(w))$ for all $g\in G$ and $w\in W$, and of an integer $d$, a basis $b_W$ of $W$ over $\mathbb{Z}/p$ and a basis $b_V$ of $V$ over $k$, both indexed by $\mathrm{Fin}\ d$, with $b_V(s)=j(b_W(s))$ for every $s$. No hypothesis on the characteristic of $k$ beyond its $\mathbb{Z}/p$-algebra structure is imposed.
--
--   This is the descent statement saying that the quotient of the Steinberg representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ by the line of constant functions is defined over the prime field, any realisation of it over a field of characteristic $p$ being obtained by base change along a term-by-term matching of bases. It is used in the comparison of Hecke eigensystems on such quotients over an extension field with those over $\mathbb{Z}/p$, where the matched bases transport the eigensystem data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_exists_semilinearMap_steinberg_quotient_forall_apply_eq_and_exists_basis_eq_of_steinberg_quotient_zmod.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
CuspidalType.exists_semilinearMap_steinberg_quotient_forall_apply_eq_and_exists_basis_eq_of_steinberg_quotient_zmod
    {q : ℕ} [Fact q.Prime] (p : ℕ) [Fact p.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
      (ρW : Representation (ZMod p) (CuspidalType.GL2 q) W)
    (πW : ↥(CuspidalType.steinberg q (ZMod p)).toSubmodule →ₗ[ZMod p] W)
    (hπW : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q (ZMod p)).toSubmodule,
        πW ⟨CuspidalType.ind q (ZMod p) g v, (CuspidalType.steinberg q (ZMod p)).apply_mem_toSubmodule g v.2⟩ =
          ρW g (πW v))
    (hπWsurj : Function.Surjective πW)
    (hπWker : ∀ v : ↥(CuspidalType.steinberg q (ZMod p)).toSubmodule,
        πW v = 0 ↔ ∃ c : ZMod p, (v : CuspidalType.ProjLine q →₀ ZMod p) = c • CuspidalType.constFun q (ZMod p))
    (k : Type) [Field k] [Algebra (ZMod p) k]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q k).toSubmodule →ₗ[k] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q k).toSubmodule,
        π ⟨CuspidalType.ind q k g v, (CuspidalType.steinberg q k).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q k).toSubmodule,
        π v = 0 ↔ ∃ c : k, (v : CuspidalType.ProjLine q →₀ k) = c • CuspidalType.constFun q k)
    :
    ∃ j : W →ₛₗ[algebraMap (ZMod p) k] V,
      (∀ (g : CuspidalType.GL2 q) (w : W), j (ρW g w) = ρ g (j w)) ∧
        ∃ (d : ℕ) (bW : Module.Basis (Fin d) (ZMod p) W) (bV : Module.Basis (Fin d) k V),
          ∀ s : Fin d, bV s = j (bW s) := by sorry
