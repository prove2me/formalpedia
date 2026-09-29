-- Prove2me | Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient
-- name    : AutomorphicForm.hasSum_whittakerCoefficient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/13d1825f-c85b-5930-8321-223d1e830006
-- title:
--   Whittaker–Fourier expansion of a continuous unipotent slice
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for the adelic general linear group in the project's sense. Fix auxiliary data: a subset $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$, an assignment $U$ of a subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ to each ideal of $\mathcal{O}_F$, and an assignment $\mathrm{gen}$ of an element of $\mathrm{GL}_2(\mathbb{A}_F)$ to each height-one prime of $\mathcal{O}_F$; these enter only as components of the bundled data `productionPinsOf F D U gen (adelicBox F)`, whose measure-theoretic part is the Borel structure on $\mathbb{A}_F$ together with the conditional probability measure $\nu$ obtained from additive adelic Haar measure by conditioning on the box $B = \{x : x_\infty \in \mathcal{F},\ x_{\mathrm{fin}} \text{ integral at every finite place}\}$, $\mathcal{F}$ the fundamental domain of the lattice basis of the mixed embedding. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is continuous, non-trivial and trivial on the image of $F$, let $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function and $g \in \mathrm{GL}_2(\mathbb{A}_F)$. Assume the unipotent slice $x \mapsto \varphi(n(x)g)$ is continuous, where $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$, and assume the family of coefficients $W_\alpha(g) = \int \varphi(n(x)g)\,\psi(-\alpha x)\,d\nu(x)$, indexed by $\alpha \in F$ (with $\alpha$ mapped into $\mathbb{A}_F$), is summable. Then this family has sum $\varphi(g)$.
--
--   This is the global Fourier–Whittaker expansion along the unipotent radical of the Borel subgroup of $\mathrm{GL}_2$, with the Fourier coefficients taken against the normalised (probability) conditional Haar measure on the standard adelic box fundamental domain, evaluated at the identity of the slice. It is the expansion step used in the project's treatment of Eisenstein series — the decomposition of a Bruhat-type Eisenstein series into its constant term plus the sum of its Whittaker coefficients, the associated analytic continuation statements — and in the vanishing criteria for cuspidal functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasSum_whittakerCoefficient.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox

theorem AutomorphicForm.hasSum_whittakerCoefficient
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g)) :
    HasSum (fun α : F =>
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g)
      (φ g) := by sorry
