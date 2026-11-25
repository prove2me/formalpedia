-- Prove2me | Theorems.Thm_Arxiv1904_10695_reference_amplitude_from_tm
-- name    : Arxiv1904_10695.reference_amplitude_from_tm
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:36:12.904362+00:00
-- url     : https://prove2.me/theorems/8e898505-1866-44d1-b3f8-b861f9e70989
-- title:
--   Eq. (2): the reference amplitude profile from the observed transmission matrix
-- statement:
--   Let $M,N\ge1$. Let $t=(t_{mn})\in\mathbb{C}^{M\times N}$ be a transmission matrix from $M$ input modes to $N$ output pixels, let $E_{ref}\in\mathbb{C}^N$ be the output reference field, and let $t_{obs,mn}=t_{mn}E_{ref,n}$ be the observed transmission matrix. Write $\langle a_m\rangle_m=\frac1M\sum_{m=1}^M a_m$.
--
--   1. For every output pixel $n$,
--   $$\langle|t_{obs,mn}|\rangle_m=\langle|t_{mn}|\rangle_m\,|E_{ref,n}|.$$
--   2. Suppose in addition that $\langle|t_{mn}|\rangle_m$ does not depend on $n$ (spatial homogeneity), that $t\ne0$ and that $E_{ref}\ne0$. Then there is a constant $c>0$ with
--   $$\langle|t_{obs,mn}|\rangle_m=c\,|E_{ref,n}|\quad\text{for every }n,$$
--   and normalising by the maximum over the output pixels recovers the reference amplitude profile:
--   $$\frac{\langle|t_{obs,mn}|\rangle_m}{\max_{n'}\langle|t_{obs,mn'}|\rangle_m}=\frac{|E_{ref,n}|}{\max_{n'}|E_{ref,n'}|}\quad\text{for every }n.$$
--
--   This is eq. (2) of the paper. It is the basis of the paper's estimate of the reference speckle amplitude from one transmission-matrix measurement, which then decides which rows of the matrix are corrected.
--
--   **Formalization Note** The paper says the constant is spatially homogeneous "since each input mode gives a speckle of same mean intensity". That property does not imply that $\langle|t_{mn}|\rangle_m$ is independent of $n$, so the independence is stated as an explicit hypothesis of part 2. The hypotheses $t\ne0$ and $E_{ref}\ne0$ make $c>0$ and keep the normalisation from dividing by zero; the paper assumes them implicitly. Part 1 needs neither. The paper writes $t_{obs,mn}=t_{mn}E_{ref,n}$. A correct expansion of eq. (1) gives $t_{mn}\overline{E_{ref,n}}$, which has the same modulus, so the statement does not change.
-- source:
--   Hofer and Brasselet, Manipulating the transmission matrix of scattering media for nonlinear imaging beyond the memory effect, arXiv:1904.10695v1 (2019), claim c003; Section 1 (Introduction), eq. (2) and the sentences before and after it, PDF p. 3; t_obs = t E_ref from eq. (1), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1904_10695_Basic

open Arxiv1904_10695

namespace Arxiv1904_10695

theorem reference_amplitude_from_tm {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (t : TransmissionMatrix M N) (Eref : Fin N → ℂ) :
    (∀ n, ampAvg (obsTM t Eref) n = ampAvg t n * ‖Eref n‖) ∧
    ((∀ n n', ampAvg t n = ampAvg t n') → t ≠ 0 → Eref ≠ 0 →
      (∃ c : ℝ, 0 < c ∧ ∀ n, ampAvg (obsTM t Eref) n = c * ‖Eref n‖) ∧
      (∀ n, normalizeByMax (ampAvg (obsTM t Eref)) n =
        normalizeByMax (fun n' => ‖Eref n'‖) n)) := by sorry

end Arxiv1904_10695
