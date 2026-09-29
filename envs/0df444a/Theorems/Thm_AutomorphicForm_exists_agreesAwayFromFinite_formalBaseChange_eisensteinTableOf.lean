-- Prove2me | Theorems.Thm_AutomorphicForm_exists_agreesAwayFromFinite_formalBaseChange_eisensteinTableOf
-- name    : AutomorphicForm.exists_agreesAwayFromFinite_formalBaseChange_eisensteinTableOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/970b4078-6c84-5118-a0ab-7f85e0bd963b
-- title:
--   Base change of an Eisenstein Hecke table is Eisenstein
-- statement:
--   Let $K$ and $M$ be number fields with $M$ a $K$-algebra, equipped with a compatible algebra map $\mathcal{O}_K \to \mathcal{O}_M$ that is integral and forms a scalar tower with $\mathcal{O}_K \to \mathcal{O}_M \to M$; let $N \subseteq \mathcal{O}_K$ be a nonzero ideal, and let $\mu_1, \mu_2 \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be continuous monoid homomorphisms on the ideles of $K$ which are idele class characters in the sense that each is trivial on the image of every $u \in K^\times$. Then there exist continuous monoid homomorphisms $\nu_1, \nu_2 \colon (\mathbb{A}_M)^\times \to \mathbb{C}^\times$, each trivial on the image of $M^\times$, and a nonzero ideal $N' \subseteq \mathcal{O}_M$, such that the formal base change from $K$ to $M$ of the Eisenstein Hecke eigensystem attached to $(N, \mu_1, \mu_2)$ agrees away from a finite set of primes with the Eisenstein Hecke eigensystem attached to $(N', \nu_1, \nu_2)$. Concretely, the Eisenstein eigensystem `eisensteinTableOf K N hN μ₁ μ₂` has level $N$ and, at a height-one prime $v$ of $\mathcal{O}_K$, data $a_v = \mu_1(\varpi_v) + \mu_2(\varpi_v)$ and $b_v = \mu_1(\varpi_v)\mu_2(\varpi_v)$, where $\varpi_v$ is the idele which is a chosen uniformiser at $v$ and trivial elsewhere; its formal base change has level $\top$ and, at a prime $\mathfrak{P}$ of $\mathcal{O}_M$ lying under $v = \mathfrak{P} \cap \mathcal{O}_K$ with inertia degree $f$, data $\mathrm{satakePow}_f(a_v, b_v)$ and $b_v^{\,f}$, where $\mathrm{satakePow}$ is the recursion $s_0 = 2$, $s_1 = s$, $s_{n+2} = s\,s_{n+1} - e\,s_n$. The conclusion asserts the existence of a finite set $S$ of height-one primes of $\mathcal{O}_M$ outside which these two values coincide with $\nu_1(\varpi_{\mathfrak{P}}) + \nu_2(\varpi_{\mathfrak{P}})$ and $\nu_1(\varpi_{\mathfrak{P}})\nu_2(\varpi_{\mathfrak{P}})$ respectively; levels are not compared.
--
--   This is the Hecke-parameter form of the statement that base change takes a principal series (Eisenstein) automorphic datum for $\mathrm{GL}_2$ over $K$ to the principal series datum attached to the composites of the characters with the relative idelic norm, the $\nu_i$ and the level $N'$ being left existentially bound. It is used in the Langlands–Tunnell converse argument, where [`LanglandsTunnell.not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH`](thm.html#LanglandsTunnell.not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH) contrasts it with the base change of the quaternionic eigensystem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_agreesAwayFromFinite_formalBaseChange_eisensteinTableOf.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell LanglandsTunnell.Converse

theorem AutomorphicForm.exists_agreesAwayFromFinite_formalBaseChange_eisensteinTableOf
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [Algebra (𝓞 K) (𝓞 M)] [Algebra.IsIntegral (𝓞 K) (𝓞 M)] [IsScalarTower (𝓞 K) (𝓞 M) M]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (h₁ : IsIdeleClassChar (𝓞 K) K μ₁) (h₂ : IsIdeleClassChar (𝓞 K) K μ₂) (hc₁ : Continuous μ₁) (hc₂ : Continuous μ₂) :
    ∃ (ν₁ ν₂ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (N' : Ideal (𝓞 M)) (hN' : N' ≠ ⊥),
      IsIdeleClassChar (𝓞 M) M ν₁ ∧ IsIdeleClassChar (𝓞 M) M ν₂ ∧ Continuous ν₁ ∧ Continuous ν₂ ∧
      (formalBaseChange K M (eisensteinTableOf K N hN μ₁ μ₂)).AgreesAwayFromFinite (eisensteinTableOf M N' hN' ν₁ ν₂) := by sorry
