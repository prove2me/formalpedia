-- Prove2me | Theorems.Thm_CompressedSensingRadar_alltop_properties
-- name    : CompressedSensingRadar.alltop_properties
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:47:43.527389+00:00
-- url     : https://prove2.me/theorems/022f58df-32b4-49b9-adec-080d41dbd14d
-- title:
--   Properties 1 and 2: the Alltop Gabor frame is a union of $N$ mutually unbiased bases
-- statement:
--   Let $N\ge5$ be prime and let $f_A$ be the Alltop sequence $f_n=N^{-1/2}e^{2\pi in^3/N}$. Write $\varphi^{(k)}_j$ for the $j$-th column of $D_kW_N$ built from $f_A$. Then $\|f_A\|_2=1$, and for all $j,j',k,k'\in\{0,\dots,N-1\}$:
--
--   $$\text{(Property 1)}\quad|\langle\varphi^{(k)}_j,\varphi^{(k)}_{j'}\rangle|=\begin{cases}1,&j=j'\\0,&j\ne j'\end{cases}\qquad\text{(Property 2)}\quad|\langle\varphi^{(k)}_j,\varphi^{(k')}_{j'}\rangle|=\frac1{\sqrt N}\ \ (k\ne k').$$
--
--   Consequently the coherence of the Alltop Gabor frame is $\mu(\Phi_A)=1/\sqrt N$.
--
--   So each block is an orthonormal basis of $\mathbb{C}^N$, and the $N$ blocks are mutually unbiased. This is the incoherence on which all three theorems rest.
-- source:
--   Herman and Strohmer, High-Resolution Radar via Compressed Sensing, arXiv:0803.2257v2 (2008), Section III-D, eq. (12), Property 1 and Property 2, p. 4

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

open MeasureTheory ProbabilityTheory

namespace CompressedSensingRadar

theorem alltop_properties (N : ℕ) (hN : N.Prime) (h5 : 5 ≤ N) :
    norm2 (alltop N) = 1 ∧
    (∀ k j j' : Fin N,
      ‖ip (blockAtom N (alltop N) k j) (blockAtom N (alltop N) k j')‖ = if j = j' then 1 else 0) ∧
    (∀ k k' : Fin N, k ≠ k' → ∀ j j' : Fin N,
      ‖ip (blockAtom N (alltop N) k j) (blockAtom N (alltop N) k' j')‖ = 1 / Real.sqrt N) ∧
    coherence (gaborDict N (alltop N)) = 1 / Real.sqrt N := by sorry

end CompressedSensingRadar
