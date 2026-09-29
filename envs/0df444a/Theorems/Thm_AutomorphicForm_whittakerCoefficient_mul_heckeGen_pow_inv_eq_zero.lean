-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_inv_eq_zero
-- name    : AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_inv_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/7fdfc848-c487-5193-aaf3-759412946e99
-- title:
--   Vanishing of the Whittaker coefficient at g Gᵥ^{-(k+1)}
-- statement:
--   Let $F$ be a number field, let $D$ be a subset of $\mathrm{GL}_2$ of the adele ring of $F$, let $U$ assign to each ideal of $\mathcal O_F$ a subgroup of that group, and let $\mathrm{gen}$ assign an element of it to each finite place; these four data enter only through the package `productionPinsOf F D U gen (adelicBox F)`, whose measure-theoretic content is the Borel structure and Haar measure on $\mathrm{GL}_2$ of the adeles, the full central subgroup, and the Haar measure on the adele ring conditioned on the set `adelicBox F` of adeles whose archimedean part lies in `infiniteBox F` and whose finite part is integral. Let $\psi$ be a $\mathbb C$-valued additive character of the adele ring which is trivial on the image of $F$, and let $v$ be a finite place of $F$ such that there is $x$ in the completion $F_v$ with $\mathrm{Valued.v}\,x \le \mathrm{WithZero.exp}(1)$ and $\psi$ non-trivial on the adele [`NumberField.StandardAddChar.adeleSingleAt F v x`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L56) having $x$ in the $v$-slot and zero elsewhere. Let $\varphi : \mathrm{GL}_2(\mathbb A_F) \to \mathbb C$ satisfy: $\varphi(n(\iota(\beta)+u)h) = \varphi(n(u)h)$ for all $\beta \in F$, all adeles $u$ and all $h$, where $n(x)$ is the upper unipotent matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$; and $\varphi(x \cdot \iota_v(n(u))) = \varphi(x)$ for every $u$ in the valuation ring of $F_v$ and every $x$, where $\iota_v$ is the embedding `finEmbed ∘ localEmbed` of $\mathrm{GL}_2(F_v)$ into $\mathrm{GL}_2(\mathbb A_F)$ at $v$ (identity in the other slots). Finally let $g$ have trivial $v$-component, i.e. `finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1`, and let $k$ be a natural number. Then the Whittaker coefficient at $\alpha = 1$, namely $\int \varphi(n(x)\,h)\,\psi(-(\iota(1)x))\,d\nu(x)$ with $\nu$ the above conditioned measure, vanishes at $h = g \cdot \bigl(\mathrm{heckeGen}\,v\bigr)^{-(k+1)}$.
--
--   This is the support bound for the adelic Whittaker (Fourier) coefficients of a form that is left periodic under rational unipotents and right invariant under the local integral unipotents: translating $g$ by negative powers of the Hecke element at $v$ pushes the argument outside the support of the coefficient. It is used in the Langlands–Tunnell part of the development, in the construction of a cuspidal constituent with non-vanishing Whittaker coefficient at the identity diagonal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_inv_eq_zero.lean

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

theorem AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_inv_eq_zero
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (v : HeightOneSpectrum (𝓞 F))
    (hψv1 : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧
      ψ (NumberField.StandardAddChar.adeleSingleAt F v x) ≠ 1)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g))
    (hinv : ∀ (u : v.adicCompletionIntegers F) (x : AdelicGL2 (𝓞 F) F),
      φ (x * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (unipotentInt (v.adicCompletion F) u))) = φ x)
    (g : AdelicGL2 (𝓞 F) F) (hg : finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1) (k : ℕ) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
        (g * (heckeGen (𝓞 F) F v ^ (k + 1))⁻¹) = 0 := by sorry
