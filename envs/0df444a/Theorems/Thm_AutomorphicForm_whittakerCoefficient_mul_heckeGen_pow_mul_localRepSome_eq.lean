-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_mul_localRepSome_eq
-- name    : AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_mul_localRepSome_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/cd0a8bdd-29c2-5038-a81b-6cce3ae9ef8e
-- title:
--   Whittaker coefficient: Hecke representatives raise the exponent
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2$ of the adeles of $F$, $U$ an assignment of a subgroup of that group to each ideal of $\mathcal O_F$, and $\mathrm{gen}$ an assignment of a group element to each finite place; these three data, together with the Borel structure on the adeles and the conditional measure of adelic additive Haar measure on the box `adelicBox F`, are packaged by `productionPinsOf` into the datum with respect to which all Whittaker coefficients below are formed, so that the coefficient at $\alpha\in F$ and $h$ is $\int \varphi(n(x)h)\,\psi(-(\alpha x))$ against that conditional measure, $n(x)$ denoting the upper unipotent matrix with entry $x$. Let $\psi$ be an additive character of the adeles of $F$ with values in $\mathbb C$ that is trivial on the image of $F$, and let $v$ be a finite place of $F$ such that $\psi$ is trivial on every adele concentrated at $v$ (zero at all other places) whose $v$-component has valuation at most $1$. Let $\varpi$ lie in the valuation ring at $v$ with nonzero image in the completion $F_v$, and assume that the image in $\mathrm{GL}_2$ of the adeles of the diagonal matrix $\mathrm{diag}(\varpi,1)\in\mathrm{GL}_2(F_v)$, under the place-$v$ embedding into the finite adelic group followed by the embedding of the finite adelic group into the full adelic group, is the Hecke element `heckeGen` at $v$. Let $\varphi$ be a complex-valued function on $\mathrm{GL}_2$ of the adeles satisfying $\varphi(n(\beta+u)h)=\varphi(n(u)h)$ for all $\beta\in F$, all adeles $u$ and all $h$. Finally let $g$ be a group element whose $v$-component (of its finite-adelic part) is the identity, let $e$ be a natural number, and let $b$ lie in the valuation ring at $v$. Then the Whittaker coefficient at $\alpha=1$ of $\varphi$ evaluated at $g\cdot \mathrm{heckeGen}^e\cdot \iota_v\bigl(n(b)\,\mathrm{diag}(\varpi,1)\bigr)$ equals its value at $g\cdot \mathrm{heckeGen}^{e+1}$, where $\iota_v$ is the above embedding of $\mathrm{GL}_2(F_v)$ into $\mathrm{GL}_2$ of the adeles.
--
--   This is the step showing that, on Whittaker coefficients, the local Hecke coset representatives $n(b)\,\mathrm{diag}(\varpi,1)$ at a place $v$ of conductor zero for $\psi$ contribute exactly as the $(e+1)$-st power of the Hecke element, the unipotent factor being absorbed by the left periodicity of $\varphi$ and the triviality of $\psi_v$ on the integers. It is used in the analysis of Whittaker expansions of cusp forms entering the Langlands–Tunnell input, via the existence statement for a cuspidal constituent with nonvanishing Whittaker coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_mul_localRepSome_eq.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox AdelicDock LocalGL2

theorem AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_mul_localRepSome_eq
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (v : HeightOneSpectrum (𝓞 F))
    (hψv : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (0 : ℤ) →
      ψ (NumberField.StandardAddChar.adeleSingleAt F v x) = 1)
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hgen : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g))
    (g : AdelicGL2 (𝓞 F) F) (hg : finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1)
    (e : ℕ) (b : v.adicCompletionIntegers F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
        (g * heckeGen (𝓞 F) F v ^ e * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepSome ϖ hϖ0 b))) =
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
        (g * heckeGen (𝓞 F) F v ^ (e + 1)) := by sorry
