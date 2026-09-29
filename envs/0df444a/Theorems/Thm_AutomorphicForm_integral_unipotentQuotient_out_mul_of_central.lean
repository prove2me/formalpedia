-- Prove2me | Theorems.Thm_AutomorphicForm_integral_unipotentQuotient_out_mul_of_central
-- name    : AutomorphicForm.integral_unipotentQuotient_out_mul_of_central
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/be3cee2a-161f-5322-aa1d-f589147bf515
-- title:
--   Central translation invariance of the unipotent-quotient integral
-- statement:
--   Work with $G = \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, the general linear group of degree $2$ over the adele ring of $\mathbb{Q}$, equipped with its Borel measurable structure, and assume $G$ is second countable. Let $E$ be a real normed space, let $z \in G$ satisfy $z g = g z$ for every $g \in G$ (that is, $z$ is central), and let $f : G \to E$ be invariant under left translation by the adelic unipotent subgroup $N$, the image of the homomorphism sending an adele $x$ to the unipotent matrix $\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$: thus $f(n g) = f(g)$ for all $n \in N$ and $g \in G$. Consider the quotient $N \backslash G$ of $G$ by the orbit relation of $N$, carrying the measure obtained by pushing forward, along the quotient map, the Haar measure of $G$ weighted by the density attached to $N$ and to the measure on $N$ transported from the adelic additive Haar measure normalised so that the standard adelic box has volume $1$. Then, writing $\mathrm{out}$ for the chosen section $N\backslash G \to G$ of the quotient map, the Bochner integrals of $q \mapsto f(\mathrm{out}(q) z)$ and of $q \mapsto f(\mathrm{out}(q))$ over $N\backslash G$ agree, and the first function is integrable if and only if the second is.
--
--   This is the statement that right translation by a central element preserves the quotient (unfolded) integral over $N \backslash \mathrm{GL}_2(\mathbb{A})$ of a function invariant under the adelic unipotent subgroup, together with the accompanying transfer of integrability; centrality lets left invariance of the Haar measure of $G$ do the work. It feeds the analysis of central characters in the Rankin–Selberg step, being used in the construction of the entire, bounded-on-strips continuation of the Rankin–Selberg $L$-function attached to the relevant datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_unipotentQuotient_out_mul_of_central.lean

import Definitions.Def_AutomorphicForm_UnipotentQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.integral_unipotentQuotient_out_mul_of_central
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : AdelicGL2 (𝓞 ℚ) ℚ) (hz : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, z * g = g * z)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → E)
    (hf : ∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f g) :
    (∫ q, f (Quotient.out q * z) ∂(unipotentQuotientMeasure ℚ) =
        ∫ q, f (Quotient.out q) ∂(unipotentQuotientMeasure ℚ)) ∧
    (Integrable (fun q : UnipotentQuotient ℚ => f (Quotient.out q * z)) (unipotentQuotientMeasure ℚ) ↔
      Integrable (fun q : UnipotentQuotient ℚ => f (Quotient.out q)) (unipotentQuotientMeasure ℚ)) := by sorry
