-- Prove2me | Theorems.Thm_Arxiv2205_09423_offdiagonal_transmission_circular
-- name    : Arxiv2205_09423.offdiagonal_transmission_circular
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T12:22:53.384309+00:00
-- url     : https://prove2.me/theorems/363c863e-f4fd-5d2e-a02b-223570dcfe4e
-- title:
--   Section 2.2: off-diagonal transmission elements are circular, swapped blocks are pseudo-correlated (as proved)
-- statement:
--   Under the hypotheses of the mean transmission formula (Eq. 20), let $i\ne j$. Then:
--
--   1. every element of the off-diagonal block $\bar{\mathbf t}_{(j,i)}$ has mean $0$;
--   2. any two elements of $\bar{\mathbf t}_{(j,i)}$ have pseudo-covariance $0$, so each element is second-order circular (proper);
--   3. $\delta^P_{ijji}=1$, and for all $a,b,c,d$
--   $$\langle\bar t_{(j,i)ba}\bar t_{(i,j)dc}\rangle-\langle\bar t_{(j,i)ba}\rangle\langle\bar t_{(i,j)dc}\rangle=C_{ijji}\,\langle A^t_{(j,i)ba}A^t_{(i,j)dc}\rangle,$$
--   which is non-zero exactly when $\langle A^t_{(j,i)ba}A^t_{(i,j)dc}\rangle\ne0$.
--
--   Thus the blocks $\bar{\mathbf t}_{(j,i)}$ and $\bar{\mathbf t}_{(i,j)}$, related by exchanging incident and outgoing directions, can be pseudo-correlated, and the joint law of $\bar{\mathbf t}$ is then not circular. Here the particles of a slab of thickness $\Delta L>0$ and density $n>0$ form the ensemble of Section 2.2: the pairs $(\mathbf r_p,\mathbf A_p)$, $p=1,\dots,N$, are independent, each position is independent of the particle's morphology, the amplitude matrices are identically distributed with finite second moments, the $z$ coordinate of each centre is uniform on $[-\Delta L/2,\Delta L/2]$ and independent of its transverse position, and the transverse phase averages obey $N\langle e^{i\mathbf q\cdot\boldsymbol\rho}\rangle=(2\pi)^2n\Delta L\,\delta_{\mathbf q,\mathbf 0}/w$ for $\mathbf q=\boldsymbol\kappa_i-\boldsymbol\kappa_j-\boldsymbol\kappa_u+\boldsymbol\kappa_v$. $\langle\mathbf A^t_{(j,i)}\rangle$ etc. denote moments of the reduced amplitude matrices of one particle.
--
--   **Formalization Note** The paper says every element of an off-diagonal block is a circularly symmetric complex random variable. Under its assumption that the elements are jointly Gaussian, this is equivalent to mean zero and pseudo-variance zero. Here the second-order statement is proved without the Gaussian assumption, which the finite-$N$ model does not satisfy. The paper asserts a non-zero pseudo-correlation between $\bar{\mathbf t}_{(j,i)}$ and $\bar{\mathbf t}_{(i,j)}$ without condition. It is non-zero only when the single-particle moment $\langle A^t_{(j,i)ba}A^t_{(i,j)dc}\rangle$ is, so the statement gives the exact value and the equivalence. The treatment of the infinite-slab limit is as in Eq. (20).
-- source:
--   Byrnes and Foreman, Random matrix theory of polarized light scattering in disordered media, arXiv:2205.09423v1 (2022), claim c006; Section 2.2, paragraph after Eq. (27), PDF p. 9

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv2205_09423

theorem offdiagonal_transmission_circular {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL n : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (r : Fin N → Ω → Fin 3 → ℝ) (A : Fin N → Ω → Amp) (hE : IsSlabEnsemble K dL n P r A)
    (p0 : Fin N)
    (j i : Fin (2 * Nk + 1)) (hij : i ≠ j) :
    (∀ b a : Fin 2, ∫ ω, tbar K (fun p => A p ω) (fun p => r p ω) j i b a ∂P = 0) ∧
    (∀ b a d c : Fin 2,
      pcovC P (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) j i b a)
        (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) j i d c) = 0) ∧
    K.deltaP i j j i = 1 ∧
    (∀ b a d c : Fin 2,
      pcovC P (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) j i b a)
          (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) i j d c) =
        ((K.cijuv n dL i j j i : ℝ) : ℂ) *
          ∫ ω, ampRed K (A p0 ω) K.kvec K.kvec j i b a *
            ampRed K (A p0 ω) K.kvec K.kvec i j d c ∂P ∧
      (pcovC P (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) j i b a)
          (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) i j d c) ≠ 0 ↔
        ∫ ω, ampRed K (A p0 ω) K.kvec K.kvec j i b a *
          ampRed K (A p0 ω) K.kvec K.kvec i j d c ∂P ≠ 0)) := by sorry

end Arxiv2205_09423
