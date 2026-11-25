-- Prove2me | Theorems.Thm_Arxiv2205_09423_covariance_table_A1
-- name    : Arxiv2205_09423.covariance_table_A1
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T12:27:49.475557+00:00
-- url     : https://prove2.me/theorems/ff5e8376-ef05-4498-8f74-afe51b8a5130
-- title:
--   Table A1: covariances and pseudo-covariances of all blocks of the scattering matrix (as proved)
-- statement:
--   Under the hypotheses of the mean transmission formula (Eq. 20), let $i,j,u,v$ be modes with $(i,j)$ and $(u,v)$ not both diagonal (that is, not $i=j$ and $u=v$ at once) and $a,b,c,d\in\{\theta,\phi\}$. For each block $\bar B\in\{\bar{\mathbf t},\bar{\mathbf r},\bar{\mathbf t}',\bar{\mathbf r}'\}$ of $\bar{\mathbf S}$, with single-particle matrix $A^B_{(j,i)}$,
--
--   $$\langle\bar B_{(j,i)ba}\bar B^*_{(v,u)dc}\rangle-\langle\bar B_{(j,i)ba}\rangle\langle\bar B^*_{(v,u)dc}\rangle=\delta^R C_{ijuv}\langle A^B_{(j,i)ba}A^{B*}_{(v,u)dc}\rangle\operatorname{sinc}\Big(\frac{\Delta L}{2}s^R_B\Big),$$
--   $$\langle\bar B_{(j,i)ba}\bar B_{(v,u)dc}\rangle-\langle\bar B_{(j,i)ba}\rangle\langle\bar B_{(v,u)dc}\rangle=\delta^P C_{ijuv}\langle A^B_{(j,i)ba}A^{B}_{(v,u)dc}\rangle\operatorname{sinc}\Big(\frac{\Delta L}{2}s^P_B\Big),$$
--
--   where
--
--   | $\bar B$ | $s^R_B$ | $s^P_B$ |
--   |---|---|---|
--   | $\bar{\mathbf t}$ | $k_{iz}-k_{jz}-k_{uz}+k_{vz}$ | $k_{iz}-k_{jz}+k_{uz}-k_{vz}$ |
--   | $\bar{\mathbf r}$ | $k_{iz}+k_{jz}-k_{uz}-k_{vz}$ | $k_{iz}+k_{jz}+k_{uz}+k_{vz}$ |
--   | $\bar{\mathbf t}'$ | $-k_{iz}+k_{jz}+k_{uz}-k_{vz}$ | $-k_{iz}+k_{jz}-k_{uz}+k_{vz}$ |
--   | $\bar{\mathbf r}'$ | $-k_{iz}-k_{jz}+k_{uz}+k_{vz}$ | $-k_{iz}-k_{jz}-k_{uz}-k_{vz}$ |
--
--   These are the second-order statistics from which the random scattering matrices are generated. Here the particles of a slab of thickness $\Delta L>0$ and density $n>0$ form the ensemble of Section 2.2: the pairs $(\mathbf r_p,\mathbf A_p)$, $p=1,\dots,N$, are independent, each position is independent of the particle's morphology, the amplitude matrices are identically distributed with finite second moments, the $z$ coordinate of each centre is uniform on $[-\Delta L/2,\Delta L/2]$ and independent of its transverse position, and the transverse phase averages obey $N\langle e^{i\mathbf q\cdot\boldsymbol\rho}\rangle=(2\pi)^2n\Delta L\,\delta_{\mathbf q,\mathbf 0}/w$ for $\mathbf q=\boldsymbol\kappa_i-\boldsymbol\kappa_j-\boldsymbol\kappa_u+\boldsymbol\kappa_v$. $\langle\mathbf A^t_{(j,i)}\rangle$ etc. denote moments of the reduced amplitude matrices of one particle.
--
--   **Formalization Note** The statement is what the derivation of Eqs. (22)–(27) gives, and it differs from the printed table in four places. (1) The second single-particle factor carries the indices $(v,u)$, as in Eqs. (25) and (27), not $(j,i)$. (2) The thickness is $\Delta L$, not $L$. (3) The pseudo-covariance has no complex conjugate, as in Eq. (26); the appendix text defines it with one. (4) For $\bar{\mathbf r}'$ the regular entry is $-k_{iz}-k_{jz}+k_{uz}+k_{vz}$; the table prints $+k_{uz}-k_{vz}$, which contradicts the phase $e^{i(\widetilde{\mathbf k}_i-\mathbf k_j)\cdot\mathbf r}$ that its own pseudo entry implies. The printed table carries no index restriction. The statement excludes only the case $i=j$ and $u=v$ at once: there the finite-$N$ covariance has the extra term $-\langle\bar B_{(j,i)ba}\rangle\langle\bar B^*_{(v,u)dc}\rangle/N$, which vanishes only in the paper's limit $N\to\infty$. When exactly one of the two blocks is diagonal, both sides are $0$ ($\delta^R=\delta^P=0$). The blocks $\bar{\mathbf t}'$ and $\bar{\mathbf r}'$ are written by analogy with Eqs. (14)–(15), since the paper does not print them. The treatment of the infinite-slab limit is as in Eq. (20).
-- source:
--   Byrnes and Foreman, Random matrix theory of polarized light scattering in disordered media, arXiv:2205.09423v1 (2022), claim c023; Appendix A, Table A1, PDF p. 24 (with Eqs. (25) and (27), PDF pp. 8-9)

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv2205_09423

theorem covariance_table_A1 {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL n : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (r : Fin N → Ω → Fin 3 → ℝ) (A : Fin N → Ω → Amp) (hE : IsSlabEnsemble K dL n P r A)
    (p0 : Fin N)
    (j i v u : Fin (2 * Nk + 1)) (hdiag : ¬ (i = j ∧ u = v)) (b a d c : Fin 2) :
    let T := fun ω => tbar K (fun p => A p ω) (fun p => r p ω)
    let R := fun ω => rbar K (fun p => A p ω) (fun p => r p ω)
    let Tp := fun ω => tpbar K (fun p => A p ω) (fun p => r p ω)
    let Rp := fun ω => rpbar K (fun p => A p ω) (fun p => r p ω)
    let At := fun ω => ampRed K (A p0 ω) K.kvec K.kvec
    let Ar := fun ω => ampRed K (A p0 ω) K.kvec K.kvecT
    let Atp := fun ω => ampRed K (A p0 ω) K.kvecT K.kvecT
    let Arp := fun ω => ampRed K (A p0 ω) K.kvecT K.kvec
    let C := K.cijuv n dL i j u v
    let kz := K.kz
    covC P (fun ω => T ω j i b a) (fun ω => T ω v u d c) =
        ((K.deltaR i j u v * C * Real.sinc (dL / 2 * (kz i - kz j - kz u + kz v)) : ℝ) : ℂ) *
          ∫ ω, At ω j i b a * star (At ω v u d c) ∂P ∧
    covC P (fun ω => R ω j i b a) (fun ω => R ω v u d c) =
        ((K.deltaR i j u v * C * Real.sinc (dL / 2 * (kz i + kz j - kz u - kz v)) : ℝ) : ℂ) *
          ∫ ω, Ar ω j i b a * star (Ar ω v u d c) ∂P ∧
    covC P (fun ω => Tp ω j i b a) (fun ω => Tp ω v u d c) =
        ((K.deltaR i j u v * C * Real.sinc (dL / 2 * (-kz i + kz j + kz u - kz v)) : ℝ) : ℂ) *
          ∫ ω, Atp ω j i b a * star (Atp ω v u d c) ∂P ∧
    covC P (fun ω => Rp ω j i b a) (fun ω => Rp ω v u d c) =
        ((K.deltaR i j u v * C * Real.sinc (dL / 2 * (-kz i - kz j + kz u + kz v)) : ℝ) : ℂ) *
          ∫ ω, Arp ω j i b a * star (Arp ω v u d c) ∂P ∧
    pcovC P (fun ω => T ω j i b a) (fun ω => T ω v u d c) =
        ((K.deltaP i j u v * C * Real.sinc (dL / 2 * (kz i - kz j + kz u - kz v)) : ℝ) : ℂ) *
          ∫ ω, At ω j i b a * At ω v u d c ∂P ∧
    pcovC P (fun ω => R ω j i b a) (fun ω => R ω v u d c) =
        ((K.deltaP i j u v * C * Real.sinc (dL / 2 * (kz i + kz j + kz u + kz v)) : ℝ) : ℂ) *
          ∫ ω, Ar ω j i b a * Ar ω v u d c ∂P ∧
    pcovC P (fun ω => Tp ω j i b a) (fun ω => Tp ω v u d c) =
        ((K.deltaP i j u v * C * Real.sinc (dL / 2 * (-kz i + kz j - kz u + kz v)) : ℝ) : ℂ) *
          ∫ ω, Atp ω j i b a * Atp ω v u d c ∂P ∧
    pcovC P (fun ω => Rp ω j i b a) (fun ω => Rp ω v u d c) =
        ((K.deltaP i j u v * C * Real.sinc (dL / 2 * (-kz i - kz j - kz u - kz v)) : ℝ) : ℂ) *
          ∫ ω, Arp ω j i b a * Arp ω v u d c ∂P := by sorry

end Arxiv2205_09423
