-- Prove2me | Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat
-- name    : AutomorphicForm.exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/0c599567-b61a-5a92-ad6f-ba2d1f3dd1c6
-- title:
--   Nonvanishing Whittaker coefficient at a diagonal point over ℚ
-- statement:
--   Work over $F=\mathbb{Q}$ with $G=\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, written `AdelicGL2 (𝓞 ℚ) ℚ`. Fix carrier data: a set $D\subseteq G$, a family $U$ of subgroups of $G$ indexed by the ideals of $\mathcal{O}_{\mathbb{Q}}$, and a family $gen$ of elements of $G$ indexed by the height-one spectrum; these are assembled by `productionPinsOf` into a `CarrierPins` record whose measure on $\mathbb{A}_{\mathbb{Q}}$ is the adelic additive Haar measure conditioned on the box `adelicBox ℚ` (infinite part in the infinite box, finite part integral at every place), so that only this conditional measure enters the integrals below. Let $\varphi : G \to \mathbb{C}$ satisfy: (i) $\varphi(n(\beta+u)g)=\varphi(n(u)g)$ for every $\beta \in \mathbb{Q}$, every adele $u$ and every $g$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; (ii) $\varphi(z\cdot g)=\chi(z)\varphi(g)$ for all ideles $z$ and all $g$, where $z\cdot g$ means multiplication by the scalar matrix $z$ and $\chi : \mathbb{A}_{\mathbb{Q}}^{\times}\to\mathbb{C}$ is arbitrary; (iii) the predicate `HasArchCharacterAt₀` at the real place of $\mathbb{Q}$ for the character `archWeightCharAt Rat.isReal_infinitePlace n` with $n \in \mathbb{Z}$, namely $\varphi$ transforms under right translation by the archimedean embedding of the subgroup `rowIsometrySubgroup₀` of $\mathrm{GL}_2$ of the completion by the $n$-th power of the transported weight-one character. Let $x \in G$ have trivial finite part, $\mathrm{glFin}\,x = 1$, and suppose the Whittaker coefficient $\int \varphi(n(t)x)\,\psi_{\mathbb{Q}}(-t)\,d\nu(t)$, at $\alpha = 1$ and for the standard additive character `psiQ`, is nonzero. Then there exists an idele $a$ whose finite part is $1$ such that the same Whittaker coefficient at $\mathrm{diag}(a,1)$, given by `diagOne a`, is nonzero.
--
--   This is the normalisation step in the adelic Fourier–Whittaker expansion: using the Iwasawa decomposition at the real place, together with the unipotent periodicity, central character and weight at infinity, a point of nonvanishing of the first Whittaker coefficient may be moved to the diagonal torus $\mathrm{diag}(a,1)$ with trivial finite part. It is used in the Langlands–Tunnell part of the development, where nonvanishing of a Whittaker coefficient on such diagonal points is needed for a cuspidal constituent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hper : ∀ (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) * g) = φ (unipotentGL2 u * g))
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ)
    (hcent : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = χ z * φ g)
    (n : ℤ) (hwt : HasArchCharacterAt₀ ℚ Rat.infinitePlace (archWeightCharAt Rat.isReal_infinitePlace n) φ)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) (hx : glFin (𝓞 ℚ) ℚ x = 1)
    (hW : whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 x ≠ 0) :
    ∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
      whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 (diagOne a) ≠ 0 := by sorry
