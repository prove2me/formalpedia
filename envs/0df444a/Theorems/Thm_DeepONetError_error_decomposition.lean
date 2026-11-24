-- Prove2me | Theorems.Thm_DeepONetError_error_decomposition
-- name    : DeepONetError.error_decomposition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:30:09.3476+00:00
-- url     : https://prove2.me/theorems/58cc6b15-68a8-4d5c-b24a-bc5e58640e10
-- title:
--   Theorem 3.3 (as proved): error decomposition of a DeepONet
-- statement:
--   Consider the setting of Definition 2.1. Let $\alpha\in(0,1]$, and let $\mathrm{Lip}_\alpha(\mathcal{G})\in[0,\infty]$ be the $\alpha$-Hölder constant of $\mathcal{G}$ on the set $A$ of continuous inputs (no finiteness is assumed; if it is $\infty$ the bound holds under the conventions of $[0,\infty]$). Let the following maps be given, all Borel measurable:
--   1. an encoder $\mathcal{E}:X\to\mathbb{R}^m$;
--   2. an approximator $\mathcal{A}:\mathbb{R}^m\to\mathbb{R}^p$;
--   3. a decoder $\mathcal{D}:\mathbb{R}^m\to X$ with $\mathcal{D}(\mathcal{E}(u))\in A$ for every $u\in A$;
--   4. a projector $\mathcal{P}:L^2(U)\to\mathbb{R}^p$.
--
--   Let $\mathcal{R}(\alpha)=\tau_0+\sum_{k=1}^p\alpha_k\tau_k$ be a reconstruction with $\tau_0,\dots,\tau_p\in L^2(U)$, and $\mathbb{R}^m,\mathbb{R}^p$ carry the Euclidean norm. Then the DeepONet $\mathcal{N}=\mathcal{R}\circ\mathcal{A}\circ\mathcal{E}$ satisfies
--
--   $$\widehat{\mathcal{E}}\le\mathrm{Lip}_\alpha(\mathcal{G})\,\mathrm{Lip}(\mathcal{R}\circ\mathcal{P})\,(\widehat{\mathcal{E}}_{\mathcal{E}})^\alpha+\mathrm{Lip}(\mathcal{R})\,\widehat{\mathcal{E}}_{\mathcal{A}}+\widehat{\mathcal{E}}_{\mathcal{R}},$$
--
--   where $\widehat{\mathcal{E}}$ is the total error (2.11), and $\widehat{\mathcal{E}}_{\mathcal{E}}$, $\widehat{\mathcal{E}}_{\mathcal{A}}$ and $\widehat{\mathcal{E}}_{\mathcal{R}}$ are the encoding, approximation and reconstruction errors (3.1)-(3.3). Here $\widehat{\mathcal{E}}_{\mathcal{R}}$ is taken with respect to $\mathcal{G}_\#\mu$, and $\mathrm{Lip}(\mathcal{R}\circ\mathcal{P})$ is the Lipschitz constant on $L^2(U)$.
--
--   This is the paper's central reduction. It bounds the DeepONet error by an encoding error that depends only on $\mu$, a reconstruction error that depends only on $\mathcal{G}_\#\mu$, and a finite-dimensional neural network approximation error.
--
--   **Formalization Note** The paper does not state the hypothesis $\mathcal{D}(\mathcal{E}(u))\in A$ for $u\in A$, but its proof (Appendix C.2) uses it: it applies the Hölder bound on $A$ to the pair $(\mathcal{D}\mathcal{E}u,u)$. Without it the bound fails (see REPORT). Encoder and approximator are arbitrary Borel maps, as the paper's wording "arbitrary encoder ... approximator" and its proof allow, so the point-evaluation encoder and ReLU approximators are special cases. All quantities take values in $[0,\infty]$, with $0\cdot\infty=0$.
-- source:
--   Lanthaler, Mishra and Karniadakis, Error estimates for DeepOnets: A deep learning framework in infinite dimensions, arXiv:2102.09618v3 (2022), Section 3.2.1, Theorem 3.3, eq. (3.4), p. 11; errors (2.11), (3.1)-(3.3), p. 6 and p. 11; proof in Appendix C.2, pp. 77-78

import Mathlib
import Definitions.Def_DeepONetError_Basic

open MeasureTheory

namespace DeepONetError

theorem error_decomposition {d n m p : ℕ} {Dset : Set (Fin d → ℝ)} {U : Set (Fin n → ℝ)}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (L2 U)] [BorelSpace (L2 U)]
    (iota : X →L[ℝ] L2 Dset) (mu : Measure X) (A : Set X) (G : X → L2 U)
    (hdata : IsDeepONetData Dset U iota mu A G) (alpha : ℝ) (halpha0 : 0 < alpha)
    (halpha1 : alpha ≤ 1)
    (E : X → EuclideanSpace ℝ (Fin m)) (hE : Measurable E)
    (Apx : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin p)) (hApx : Measurable Apx)
    (tau : Fin (p + 1) → L2 U)
    (Dec : EuclideanSpace ℝ (Fin m) → X) (hDec : Measurable Dec) (hDecA : ∀ u ∈ A, Dec (E u) ∈ A)
    (Proj : L2 U → EuclideanSpace ℝ (Fin p)) (hProj : Measurable Proj) :
    totalErr mu G (fun u => trunkRec tau (Apx (E u))) ≤
      holderConst alpha G A * lipConst (fun v => trunkRec tau (Proj v)) * encErr mu E Dec ^ alpha +
        lipConst (trunkRec tau) * approxErr mu G E Apx Dec Proj +
        recErr (mu.map G) (trunkRec tau) Proj := by sorry

end DeepONetError
