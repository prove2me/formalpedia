-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_pow_of_hasKernelOfDegree
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_comp_frobenius_pow_of_hasKernelOfDegree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/1d57d43f-0335-5629-ac32-de2e7488ec10
-- title:
--   Frobenius-twisted translate of an admissible rigidified special formal module
-- statement:
--   Let $p$ be a prime and $k$ a perfect field of characteristic $p$, let $\iota : \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to W(k)$ be a ring homomorphism, and let $\Phi$ be a formal $\mathcal{O}_D$-module over $W(k)/pW(k)$ (a commutative $2$-variable formal group law with a $\mathbb{Z}_{p^2}$-action by law endomorphisms and a uniformiser series $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\mathrm{Fr}(a)]\circ\varpi$) with $\Phi$ of height $4$, i.e. $[p]_\Phi$ has kernel algebra finite and projective over the base with fibre rank $p^4$ at every field-valued point. Let $B$ be a commutative ring, $\psi : W(k) \to B$ a ring homomorphism, and $t = (X, n, \rho)$ a rigidified object over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$ (its Lie algebra splits into complementary invertible pieces), $X$ has height $4$, and $\rho$ is an $\mathcal{O}_D$-homomorphism from the base change of $\Phi$ along the residue map of $\psi$ to $\bar X = X \otimes B/pB$ whose kernel has degree $p^{4n}$. Let $e$ be an element of the centraliser, inside the endomorphism ring of the law of $\Phi$, of all the action endomorphisms $[a]_\Phi$ together with $\varpi_\Phi$, and let $m'$ be a natural number such that the series family of $e$ has kernel of degree $p^{2m'}$. Then there exists a rigidified object $t' = (X', n', \rho')$ over $B$ that is admissible for $(\iota, \psi \circ \mathrm{Fr}^{m'})$, with $X' = X$, and there exists $c \in \mathbb{N}$ with $$[p^{c+n}]_{\bar X} \circ \rho' \circ \big(X_i \mapsto X_i^{p^{m'}}\big) = [p^{c+n'}]_{\bar X} \circ \rho \circ \bar e,$$ where $\bar e$ is the reduction of the series family of $e$ along the residue map of $\psi$, and all compositions are substitutions of power series.
--
--   This is the existence half of the translation action of $GL_2(\mathbb{Q}_p) = (\mathrm{End}^0_{\mathcal{O}_D}\Phi)^\times$ on Drinfeld's moduli problem for special formal $\mathcal{O}_D$-modules, in the form of Boutot–Carayol II (9.1)–(9.2): translating an admissible rigidified object by an $\mathcal{O}_D$-linear isogeny $e$ of $\Phi$ produces another admissible object, for the structure map twisted by the power of Frobenius determined by the degree of $e$. It is used in the equivariant form of Drinfeld's representability theorem and in the construction of admissible covers of quadruples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_pow_of_hasKernelOfDegree.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_comp_frobenius_pow_of_hasKernelOfDegree
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k))) (hΦ4 : Φ.HasHeight 4)
    (B : Type u) [CommRing B] (ψ : WittVector p k →+* B) (t : Rigidified p Φ B)
    (ht : t.IsAdmissible ι ψ)
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (he : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m'))) :
    ∃ t' : Rigidified p Φ B,
      t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ∧
      t'.X = t.X ∧
      ∃ c : ℕ,
        (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
            (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ (p ^ m')) =
          (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp
            (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries)) := by sorry
