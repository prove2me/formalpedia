-- Prove2me | Theorems.Thm_AutomorphicForm_HeckeEigensystem_hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf
-- name    : AutomorphicForm.HeckeEigensystem.hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/8376de3b-e45f-5247-a248-1afb2705f9ee
-- title:
--   Fibre identity for base-change Rankin–Selberg Euler products
-- statement:
--   Let $F\subseteq E$ be number fields, let $\mathfrak f\neq 0$ be an ideal of $\mathcal O_F$, and let $\eta$ be a homomorphism from the narrow ray class group of $F$ modulo $\mathfrak f$ (the group of units of fractional ideals having valuation $0$ at every prime dividing $\mathfrak f$, modulo the narrow ray subgroup) into $\mathbb C^\times$, subject to: for every prime $w$ of $\mathcal O_E$ whose restriction $v=w\cap\mathcal O_F$ does not divide $\mathfrak f$, the order of $\eta$ on the class `primeClass F 𝔣 v` equals the residue degree `inertiaDeg'` of $w$ over $v$. Let $\pi,\pi'$ be Hecke eigensystems over $F$ with values in $\mathbb C$ (each a nonzero level ideal together with functions $a,b$ on the primes) and $\Psi$ one over $E$, and assume both `IsBaseChangeOf π Ψ` and `IsBaseChangeOf π' Ψ`: outside a finite set of primes $w$ of $E$, $\Psi.a\,w=\mathrm{satakePow}\,f(\pi.a\,v,\pi.b\,v)$ and $\Psi.b\,w=(\pi.b\,v)^{f}$ with $f$ the residue degree, and likewise for $\pi'$. Then there is a finite set $S_2$ of primes of $F$ such that for every finite $S_F\supseteq S_2$, every finite set $S_E$ of primes of $E$ consisting exactly of the primes lying over $S_F$, every $s\in\mathbb C$, every $L_E\in\mathbb C$ and every family $L_i$ indexed by $i<[E:F]$ the following holds: if the product over $w\notin S_E$ of $\bigl(\mathrm{rsEulerPoly}(\Psi.a\,w/\Psi.b\,w,\ (\Psi.b\,w)^{-1},\ \Psi.a\,w,\ \Psi.b\,w,\ 0)\bigr)^{-1}$ evaluated at $N(w)^{-s}$ converges (as a `HasProd`) to $L_E$, and for each $i$ the product over $v\notin S_F$ of the corresponding inverse Euler factor, formed from the twist of $\pi$ by the function sending $v\nmid\mathfrak f$ to $\eta^{i}(\mathrm{primeClass}\,v)$ and $v\mid\mathfrak f$ to $0$ (so its $a$ is $\chi_i(v)\pi.a\,v$ and its $b$ is $\chi_i(v)^2\pi.b\,v$) in the first two slots and from $\pi'.a\,v,\ \pi'.b\,v,\ 0$ in the remaining slots, evaluated at $N(v)^{-s}$, converges to $L_i$, then $L_E=\prod_{i<[E:F]}L_i$.
--
--   This is the global fibre identity which rewrites a Rankin–Selberg Euler product over the primes of $E$, formed from a Hecke eigensystem $\Psi$ that is a base change from $F$, as the product over $i<[E:F]$ of the corresponding Euler products over $F$ for the $\eta^{i}$-twists of $\pi$ against $\pi'$; the regrouping is along the finite fibres of $w\mapsto w\cap\mathcal O_F$, and the local input is the cyclotomic identity for the character $\eta$ whose order at $v$ is the residue degree. It is used by [`AutomorphicForm.HeckeEigensystem.exists_pow_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.HeckeEigensystem.exists_pow_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable) to conclude that two eigensystems with a common base change differ by a power of $\eta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_HeckeEigensystem_hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

theorem AutomorphicForm.HeckeEigensystem.hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (η : NarrowRayClassGroup F 𝔣 →* ℂˣ)
    (hη : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ ((w.under (𝓞 F)).asIdeal ∣ 𝔣)),
      orderOf (η (primeClass F 𝔣 (w.under (𝓞 F)) hw)) =
        (w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal)
    (π π' : HeckeEigensystem F ℂ) (Ψ : HeckeEigensystem E ℂ)
    (h : IsBaseChangeOf π Ψ) (h' : IsBaseChangeOf π' Ψ) :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ SF : Finset (HeightOneSpectrum (𝓞 F)), S₂ ⊆ SF →
      ∀ SE : Finset (HeightOneSpectrum (𝓞 E)), (∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ SF) →
        ∀ (s : ℂ) (LE : ℂ) (L : Fin (Module.finrank F E) → ℂ),
          HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ SE} =>
            ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Ψ.a w.1 / Ψ.b w.1) (Ψ.b w.1)⁻¹ (Ψ.a w.1) (Ψ.b w.1) 0).eval
              (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) LE →
          (∀ i : Fin (Module.finrank F E),
            HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ SF} =>
              ((LanglandsTunnell.RankinSelberg.rsEulerPoly
                  ((π.twist (fun v => if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0)).a v.1 /
                    (π.twist (fun v => if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0)).b v.1)
                  ((π.twist (fun v => if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0)).b v.1)⁻¹
                  (π'.a v.1) (π'.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (L i)) →
          LE = ∏ i : Fin (Module.finrank F E), L i := by sorry
